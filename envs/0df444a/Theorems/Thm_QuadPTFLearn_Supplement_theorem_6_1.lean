-- Prove2me | Theorems.Thm_QuadPTFLearn_Supplement_theorem_6_1
-- name    : QuadPTFLearn.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:42:38.038079+00:00
-- url     : https://prove2.me/theorems/e78b7923-8c21-461b-a081-8871f474665d
-- title:
--   Theorem 6.1, p.62 (corrected: with probability at least 99%; k ≥ 1) — finding a direction $\hat v$ with $h_i$-correlation $\Omega(\alpha/(k+r))$
-- statement:
--   Let $D$ be a distribution over $\mathbb R^d\times\{0,1\}$ with $D_x=N(0,I_d)$, and write $h_i$ for the normalized probabilists' Hermite polynomials. There is an algorithm, given a degree budget $\ell$ and $\alpha\in(0,1)$, with the following guarantee. Suppose there are a unit vector $v\in\mathbb S^{d-1}$, an integer $k\ge1$ and a polynomial $p(w)$ on $v^\perp$ of degree at most $r=\ell-k$ with $\|p\|_2\le1$ such that
--   $$\bigl|\mathbb E_{(x,y)\sim D}[y\,h_k(v\cdot x)\,p(w)]\bigr|>\alpha,\qquad w=\mathrm{proj}_{v^\perp}x .$$
--   Then the algorithm draws at most $C\,d^{\,r+k}(1/\alpha)^C$ examples from $D$ and runs in time $C\,(d^{\,r+k}/\alpha)^C$. **With probability at least $99\%$** it outputs a direction $\hat v$ for which there are an integer $i\ge1$ and a polynomial $q(\hat w)$ on $\hat v^\perp$ with $\|q\|_2\le1$, $i+\deg q\le r+k$, and
--   $$\bigl|\mathbb E_{(x,y)\sim D}[y\,h_i(\hat v\cdot x)\,q(\hat w)]\bigr|>c\,\frac{\alpha}{k+r}.$$
--   Here $C$ and $c>0$ are universal constants.
--
--   The theorem converts the existence of a correlated direction (supplied by Theorem 5.1 whenever the target has large randomized error along some direction) into an efficiently found direction with comparable correlation. Theorem 6.2 is its one-shot version that finds all such directions.
--
--   **Formalization Note** One program and the constants $C$, $c$ are chosen before $d$, $\ell$, $\alpha$ and $D$. The output is a count $1$ and one nonzero vector $u$, and $\hat v=u/\|u\|$.
--
--   Differences from the source:
--   - correction: it draws … and outputs a vector v̂ such that … (no probability qualifier) → with probability at least 99/100 the output is such a vector; reason: no algorithm using finitely many samples meets the printed claim. Counterexample, every assumption of the source holding: d = 2, ℓ = r + k = 1 (k = 1, r = 0, p ≡ 1), α = 1/10, targets y = 1{u·x ≥ 0} for unit u with u·e₁ > 1/R, for which E[y h₁(u·x)] = 1/√(2π) > α. With positive probability all N samples lie in the unit ball around R·e₁, where every such target gives label 1, so the output v̂ is the same for all of them. The only witness allowed (i = 1, q constant, |q| ≤ 1) has |E[y h₁(v̂·x) q]| ≤ |u·v̂|/√(2π). Averaging over u in the allowed arc, some u has |u·v̂| < c·α·√(2π) with positive probability once R is large (R chosen after c). The 99% is the confidence of Lemma 6.3, from which the proof derives the theorem, and the same correction as the published theorem_6_2
--   - reading: there exists some polynomial q(ŵ) … that satisfies |E[y h_i(v̂·x) q(ŵ)]| > Ω(α/(k + r)), where i + deg(q) ≤ r + k (i unrestricted) → some i ≥ 1 and some q on v̂⊥ with ∥q∥₂ ≤ 1 and i + deg q ≤ ℓ; reason: the proof concludes B_i(u) ≥ Ω(α/ℓ) for some i ∈ [ℓ]; i ≥ 1 is the stronger reading (with i = 0 the conclusion would not involve v̂ at all)
--   - correction: k ∈ ℕ → k ≥ 1; reason: at k = 0 the conclusion is undefined for r = 0 (α/(k + r) = α/0), and for r ≥ 1 it is false under the reading i ≥ 1: take y ≡ 1 (Gaussian marginal) and p(w) = (1 + w₁)/√2 on v⊥, so ∥p∥₂ = 1 and E[y h₀(v·x) p(w)] = 1/√2 > α for α < 1/√2, while E[y h_i(v̂·x) q(ŵ)] = E[h_i(v̂·x)]·E[q(ŵ)] = 0 for every i ≥ 1; Theorem 6.2 states k ≥ 1
--   - reading: a degree r polynomial p(w); the algorithm is given α (and implicitly r + k) → the program's input is [ℓ, α] with ℓ = r + k, and the hypothesis is satisfied by any unit v, k ≥ 1 and p on v⊥ with k + deg p ≤ ℓ (degree at most r = ℓ − k); reason: the stated sample bound depends on r + k, so the algorithm must be told the degree budget (Algorithm 3's input ℓ); 'degree at most r' admits more instances, the stronger reading
--   - reading: "there is an algorithm … uses/draws … samples, runs in … time", model unspecified → one admissible program of the deterministic arithmetic sampling real RAM (exact + − × ÷, comparisons, pointers; no √, exp, log, floor, coin; unit cost, `sample` costs d+1), chosen before every parameter and the distribution, with samples and work bounded on every sample stream; reason: the paper fixes no model and its proofs count arithmetic operations; a single uniform program with worst-case bounds is the non-weaker reading (the convention of the published theorem_1_3)
--   - encoding: draws d^{(r+k)}poly(1/α) examples, runs in poly(d^{r+k}/α) time; Ω(α/(k + r)) → samples ≤ C·d^{ℓ}·(1/α)^C, work ≤ C·(d^{ℓ}/α)^C, correlation > c·α/ℓ, with one C : ℕ and one c > 0 chosen with the program; reason: the meaning of poly and Ω; the printed exponent r + k of d is kept literally
--   - encoding: outputs a vector v̂; q(ŵ) with ŵ the component of x orthogonal to v̂ → outputs (decodeVecs, count 1) a nonzero vector u, read as the unit direction v̂ = u/∥u∥; q is a polynomial on v̂⊥ (IsOnPerp); a count other than 1 or u = 0 is a failure; reason: the machine has no square root and cannot normalize; h_i(v̂·x) and proj_{v̂⊥} are meaningful for the unit vector v̂
--   - encoding: D over ℝᵈ × {0, 1} with D_x = N(0, I); v ∈ S^{d−1}; p(w) with ∥p(w)∥ ≤ 1 → a probability law on ℝᵈ × ℝ with marginal N(0, I_d) and labels in {0,1} a.s.; ∥v∥ = 1; p on v⊥ with Gaussian L² norm ≤ 1; reason: the same objects; the norm of §2 is the Gaussian L² norm
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 6.1, pp.62–63 (PDF pp.64–65); Algorithm 3 (CorrelationFinding), p.62 (PDF p.64); proof, p.64 (PDF p.66)

import Mathlib
import Definitions.Def_QuadPTFLearn_Influence
import Definitions.Def_QuadPTFLearn_Learner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

namespace Supplement

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 6.1, pp.62–63 (PDF pp.64–65), corrected: "with probability at least 99%" and `k ≥ 1`.

Let `D` be a distribution over `ℝᵈ × {0, 1}` with `D_x = N(0, I)`. There is an algorithm such
that for `α ∈ (0, 1)` and a degree budget `ℓ = r + k`: if there are a unit vector `v`, an integer
`k ≥ 1` and a polynomial `p(w)` on `v⊥` of degree at most `r = ℓ − k` with `‖p‖₂ ≤ 1` and
`|E_D[y h_k(v · x) p(w)]| > α`, then it draws at most `C d^{ℓ} (1/α)^C` examples, works at most
`C (d^ℓ/α)^C`, and with probability at least `99%` outputs a nonzero vector `u`, read as the
direction `v̂ = u/‖u‖`, such that some `i ≥ 1` and some polynomial `q(ŵ)` on `v̂⊥` with
`‖q‖₂ ≤ 1` and `i + deg q ≤ ℓ` satisfy `|E_D[y h_i(v̂ · x) q(ŵ)]| > c α/ℓ`.

**Formalization Note.** One program, one `C : ℕ` and one `c > 0` (the `Ω`) before `d, ℓ, α, D`.
Input `[ℓ, α]`; output a count `1` and one vector of `ℝᵈ` from cell `p[1]` (`decodeVecs`). The
√-free machine cannot normalize, so the output is a nonzero vector read as a direction; a count
other than `1` or the zero vector is a failure. "Degree r" is read as degree at most `r`. -/
theorem theorem_6_1 :
    ∃ P : Program, Admissible P ∧ ∃ C : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ d ℓ : ℕ, ∀ α : ℝ, 0 < α → α < 1 →
      ∀ (D : Measure (Pt d × ℝ)) [IsProbabilityMeasure D], IsBoolGaussLaw D →
        (∃ v : Pt d, ‖v‖ = 1 ∧ ∃ k : ℕ, 1 ≤ k ∧ ∃ p : Poly d, IsOnPerp v p ∧
          k + p.totalDegree ≤ ℓ ∧ l2norm (peval p) ≤ 1 ∧
          α < |∫ z, z.2 * hnorm k ⟪v, z.1⟫ * peval p z.1 ∂D|) →
        HaltsWithin P (d + 1) (initState (d + 1) [(ℓ : ℝ), α])
            (C * (d : ℝ) ^ ℓ * (1 / α) ^ C) (C * ((d : ℝ) ^ ℓ / α) ^ C) ∧
        SucceedsWP P (d + 1) (initState (d + 1) [(ℓ : ℝ), α])
          (Measure.infinitePi (fun _ : ℕ => jointLaw D)) (99 / 100)
          (fun s => ∃ u : Pt d, decodeVecs d (outMem s) (outBase s) = some [u] ∧ u ≠ 0 ∧
            ∃ i : ℕ, 1 ≤ i ∧ ∃ q : Poly d, IsOnPerp (‖u‖⁻¹ • u) q ∧ l2norm (peval q) ≤ 1 ∧
              i + q.totalDegree ≤ ℓ ∧
              c * α / ℓ < |∫ z, z.2 * hnorm i ⟪‖u‖⁻¹ • u, z.1⟫ * peval q z.1 ∂D|) := by sorry

end Supplement

end QuadPTFLearn
