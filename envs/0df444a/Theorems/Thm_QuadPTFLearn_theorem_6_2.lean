-- Prove2me | Theorems.Thm_QuadPTFLearn_theorem_6_2
-- name    : QuadPTFLearn.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:25:41.673309+00:00
-- url     : https://prove2.me/theorems/cfe4ab87-c6c7-4db0-add2-ec632fe5782f
-- title:
--   Theorem 6.2, p.63 (corrected: "with probability at least 99%") — a subspace $V$ of dimension $O(\ell/\beta^2)$ capturing all directions with $h_k$-correlation above $\beta$
-- statement:
--   Let $D$ be a distribution over $\mathbb R^d\times\{0,1\}$ with $D_x=N(0,I)$ and $\ell\ge1$. There is an algorithm such that, for $\beta\in(0,1)$, it draws $d^{O(\ell)}\mathrm{poly}(1/\beta)$ examples from $D$, runs in $\mathrm{poly}(d^\ell/\beta)$ time and, **with probability at least $99\%$**, outputs a subspace $V\subseteq\mathbb R^d$ of dimension at most $O(\ell/\beta^2)$ such that for every unit vector $v\perp V$,
--   $$\sup_{p,k:\ \|p\|=1,\ k+\deg(p)\le\ell,\ k\ge1}\ \mathbb E_{(x,y)\sim D}\big[y\,h_k(v\cdot x)\,p(w)\big]\le\beta,$$
--   where $p$ ranges over polynomials on $v^\perp$ and $w=\mathrm{proj}_{v^\perp}x$.
--
--   This is the one-shot dimension-reduction step of the learner: combined with Theorem 5.1, every direction outside $V$ has small randomized error.
--
--   **Formalization Note** One program and one constant $C$: samples $\le C d^{C\ell}(1/\beta)^C$, work $\le C(d^\ell/\beta)^C$, $\dim V\le C\ell/\beta^2$. The output is a count $r$ followed by $r$ vectors of $\mathbb R^d$, and $V$ is their span.
--
--   Differences from the source:
--   - correction: outputs a subspace V … such that … (no probability qualifier) → with probability at least 99/100; reason: no algorithm using finitely many samples meets the printed claim: take f*(x) = 1{x₁ ≥ 0}, ℓ = 1, β = 1/10, d above the dimension bound; with positive probability every sample lies in a region where all targets 1{u·x ≥ 0}, u in an open set of directions, give the same labels, so the output V is the same for all of them, has dimension < d, and misses some such u, for which E[y h₁(u·x)] > β; 99% is the confidence of Lemma 6.3, from which the proof derives the theorem
--   - reading: "there is an algorithm … using … samples and time", model unspecified → one admissible program of the deterministic arithmetic sampling real RAM (exact + − × ÷, comparisons, pointers; no √, exp, log, floor, coin; unit cost, `sample` costs d+1), chosen before every parameter and the distribution, with samples and work bounded on every sample stream; reason: the paper fixes no model and its proofs count arithmetic operations; a single uniform program with worst-case bounds is the non-weaker reading
--   - encoding: d^{O(ℓ)}poly(1/β) examples, poly(d^ℓ/β) time, dimension O(ℓ/β²) → samples ≤ C d^{Cℓ}(1/β)^C, work ≤ C(d^ℓ/β)^C, dim V ≤ Cℓ/β², one C chosen with the program; reason: the meaning of O and poly for β < 1, d ≥ 1
--   - encoding: for every v ⊥ V, sup … ≤ β → for every unit v ∈ V⊥, every k ≥ 1 and every polynomial p on v⊥ with ∥p∥₂ = 1 and k + deg p ≤ ℓ, the expectation is ≤ β; reason: a supremum is ≤ β iff every term is; v is a unit vector as in h_k(v·x) and proj_{v⊥}
--   - encoding: outputs a subspace V → a count r and r vectors of ℝᵈ from memory cell p[1]; V is their span; reason: output convention
--   - encoding: D over ℝᵈ × {0,1} with D_x = N(0, I); an ambient dimension d → a probability law on ℝᵈ × ℝ with marginal N(0, I_d), labels in {0,1} a.s.; 1 ≤ d; reason: the same laws; d^{O(ℓ)} vanishes at d = 0
--   - encoding: ℓ ∈ ℕ₊ fixed, then for β ∈ (0, 1) → input list [ℓ, β] in memory from cell 0, d + 1 in pointer register 0; reason: input convention of the machine; one program for every ℓ
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 6.2, p.63 (PDF p.65)

import Mathlib
import Definitions.Def_QuadPTFLearn_Influence
import Definitions.Def_QuadPTFLearn_Learner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 6.2, p.63 (PDF p.65), corrected: "with probability at least 99%".

Let `D` be a distribution over `ℝᵈ × {0, 1}` with `D_x = N(0, I)` and `ℓ ≥ 1`. There is an
algorithm such that for `β ∈ (0, 1)` it draws `d^{O(ℓ)} poly(1/β)` examples, runs in
`poly(d^ℓ/β)` time and, with probability at least 99%, outputs a subspace `V ⊆ ℝᵈ` of dimension
at most `O(ℓ/β²)` such that for every unit `v ⊥ V`,
`sup_{p, k : ‖p‖ = 1, k + deg(p) ≤ ℓ, k ≥ 1} E_{(x,y)∼D}[y h_k(v · x) p(w)] ≤ β`.

**Formalization Note.** The printed statement has no probability qualifier, which no algorithm
using finitely many samples can meet (see the item's differences). One program and one `C`
before `d, ℓ, β, D`: samples `≤ C d^{Cℓ} (1/β)^C`, work `≤ C (d^ℓ/β)^C`, dimension `≤ Cℓ/β²`.
Input `[ℓ, β]`; output a count `r` and `r` vectors of `ℝᵈ` from cell `p[1]`, `V` their span.
`p` ranges over polynomials on `v⊥`. -/
theorem theorem_6_2 :
    ∃ P : Program, Admissible P ∧ ∃ C : ℕ,
      ∀ d ℓ : ℕ, 1 ≤ d → 1 ≤ ℓ → ∀ β : ℝ, 0 < β → β < 1 →
      ∀ (D : Measure (Pt d × ℝ)) [IsProbabilityMeasure D], IsBoolGaussLaw D →
        HaltsWithin P (d + 1) (initState (d + 1) [(ℓ : ℝ), β])
            (C * (d : ℝ) ^ (C * ℓ) * (1 / β) ^ C) (C * ((d : ℝ) ^ ℓ / β) ^ C) ∧
        SucceedsWP P (d + 1) (initState (d + 1) [(ℓ : ℝ), β])
          (Measure.infinitePi (fun _ : ℕ => jointLaw D)) (99 / 100)
          (fun s => ∃ vs : List (Pt d), decodeVecs d (outMem s) (outBase s) = some vs ∧
            (Module.finrank ℝ (Submodule.span ℝ {x | x ∈ vs}) : ℝ) ≤ C * ℓ / β ^ 2 ∧
            ∀ v ∈ (Submodule.span ℝ {x | x ∈ vs})ᗮ, ‖v‖ = 1 →
              ∀ kk : ℕ, 1 ≤ kk → ∀ p : Poly d, IsOnPerp v p → l2norm (peval p) = 1 →
                kk + p.totalDegree ≤ ℓ →
                ∫ z, z.2 * hnorm kk ⟪v, z.1⟫ * peval p z.1 ∂D ≤ β) := by sorry

end QuadPTFLearn
