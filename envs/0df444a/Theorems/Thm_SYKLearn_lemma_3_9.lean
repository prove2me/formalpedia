-- Prove2me | Theorems.Thm_SYKLearn_lemma_3_9
-- name    : SYKLearn.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:09.847097+00:00
-- url     : https://prove2.me/theorems/8dbd8c13-0c8f-4cbe-89fa-e58526fe52aa
-- title:
--   Lemma 3.9 — Hermite tail bound for $z_O=\mathrm{Tr}[Oe^{-\beta H}]/\mathbb E Z_H$
-- statement:
--   Let $O=\Gamma_J$ be a Majorana monomial of even weight $w=|J|$ (operator norm $1$), and $z_O=\mathrm{Tr}[Oe^{-\beta H_g}]/\mathbb E_gZ_{H_g}$ with $Z_H=\mathrm{Tr}[e^{-\beta H}]$. Norms are Gaussian $L^p$ norms over the couplings, $\|f\|_{L^p}=(\mathbb E|f|^p)^{1/p}$.
--
--   1. For every $p\ge2$, even $w\ge0$ and integer $k\ge0$ there is $C_{p,w,k}$, independent of $n$ and $\beta$, such that for $\beta\ge0$ and $n\ge C_{p,w,k}(1+\beta^2)^2$,
--   $$\Big\|z_O-\sum_{d=0}^k\Pi_dz_O\Big\|_{L^p}\le e^{C_{p,w,k}(1+\beta^2)}\,n^{-(k+1)/2-w/4}.$$
--   2. For every $p\ge2$, even $w$ and $d\ge1$ there is $C_{p,d,w}$ such that $\|\Pi_dz_O\|_{L^p}\le C_{p,d,w}\,\beta^d\,n^{-d/2-w/4}$ for all $\beta\ge0$ and $n$.
--   3. For every $p\ge2$ there is $C_p$ such that $\|z_0-1\|_{L^p}\le e^{C_p(1+\beta^2)}n^{-1}$ for $\beta\ge0$ and $n\ge C_p(1+\beta^2)^2$, where $z_0=z_I$.
--
--   The tail bound lets the direction analysis truncate the Hermite expansion of $\bar\rho_4,\bar\rho_8$ after degrees $2$ and $4$ with error $e^{O(1+\beta^2)}n^{-1/2}$, at every fixed temperature.
--
--   **Formalization Note** The $L^p$ norm is Mathlib's `eLpNorm`, which is $+\infty$ for a function without a finite $p$-th moment. Each clause has its own constant, chosen after its fixed parameters and before $\beta,n$.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - reading: “For each fixed d ≥ 1, one also has ‖Π_d z_O‖_{L^p} ≤ C_{p,d,w}β^d n^{−d/2−w/4}” (no size condition attached) → clause 2 for all β ≥ 0 and all n, with no size condition; reason: the page attaches the size condition to (44) and, “under the corresponding size condition”, to the z_0 bound only; the proof derives clause 2 from [SZ26]'s bound a_d ≤ C_w d^w n^{−w/2}(Cβ²d/n)^d, for which it states no size condition. This is the stronger of the two readings
--   - encoding: a weight-w norm-one monomial O → O = Γ_J = rawString Q J with |J| = w; reason: the monomials Γ_J are unitary; a unimodular phase does not change |z_O| or its Hermite projections' norms
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 3.9, (44), p.30

import Mathlib
import Definitions.Def_SYKLearn_Hermite

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 3.9 (Hermite tail bound)**, p.30 (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning
SYK Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). Fix `p ≥ 2`, an even
Majorana weight `w ≥ 0`, and an integer `k ≥ 0`. For a weight-`w` norm-one monomial `O`, let
`z_O = Tr[Oe^{−βH}]/E Z_H`. There is a constant `C_{p,w,k}`, independent of `n` and `β`, such that,
for `β ≥ 0` and `n ≥ C_{p,w,k}(1 + β²)²`,
`‖z_O − Σ_{d=0}^k Π_d z_O‖_{L^p} ≤ e^{C_{p,w,k}(1+β²)} n^{−(k+1)/2−w/4}` (44). For each fixed
`d ≥ 1`, one also has `‖Π_d z_O‖_{L^p} ≤ C_{p,d,w} β^d n^{−d/2−w/4}`. Finally,
`‖z_0 − 1‖_{L^p} ≤ e^{C_p(1+β²)} n^{−1}` under the corresponding size condition.

**Formalization Note.** The weight-`w` norm-one monomials are `Γ_J = rawString Q J`, `|J| = w`
(unitary, operator norm `1`). `‖f‖_{L^p} = (E|f|^p)^{1/p}` is Mathlib's `eLpNorm` with respect to
`disorderLaw Q` (it is `∞` for a function without finite `p`-th moment, so no integrability is
assumed silently). `Π_d` is `hermProj` with `σ = σ_N`. The three clauses are the three conjuncts,
each with its own constant chosen after its fixed parameters and before `β, n`. The second clause
carries no size condition: the page attaches the size condition `n ≥ C(1+β²)²` to (44) and,
"under the corresponding size condition", to the third clause only. `z_0 = zO β Q 1`. `Q.J = 1`;
every CAR family. -/
theorem lemma_3_9 :
    (∀ p : ℝ, 2 ≤ p → ∀ wt k : ℕ, Even wt → ∃ C : ℝ, 0 < C ∧
      ∀ β : ℝ, 0 ≤ β → ∀ (N : ℕ) (Q : Model N), Q.J = 1 → C * (1 + β ^ 2) ^ 2 ≤ N →
        ∀ J : Finset (Fin N), J.card = wt →
          eLpNorm (fun g => zO β Q (rawString Q J) g -
              ∑ d ∈ Finset.range (k + 1),
                hermProj (sigma N) (disorderLaw Q) d (zO β Q (rawString Q J)) g)
            (ENNReal.ofReal p) (disorderLaw Q) ≤
          ENNReal.ofReal (Real.exp (C * (1 + β ^ 2)) *
            (N : ℝ) ^ (-(((k : ℝ) + 1) / 2 + (wt : ℝ) / 4)))) ∧
    (∀ p : ℝ, 2 ≤ p → ∀ wt d : ℕ, Even wt → 1 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ β : ℝ, 0 ≤ β → ∀ (N : ℕ) (Q : Model N), Q.J = 1 →
        ∀ J : Finset (Fin N), J.card = wt →
          eLpNorm (hermProj (sigma N) (disorderLaw Q) d (zO β Q (rawString Q J)))
            (ENNReal.ofReal p) (disorderLaw Q) ≤
          ENNReal.ofReal (C * β ^ d * (N : ℝ) ^ (-((d : ℝ) / 2 + (wt : ℝ) / 4)))) ∧
    (∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
      ∀ β : ℝ, 0 ≤ β → ∀ (N : ℕ) (Q : Model N), Q.J = 1 → C * (1 + β ^ 2) ^ 2 ≤ N →
        eLpNorm (fun g => zO β Q 1 g - 1) (ENNReal.ofReal p) (disorderLaw Q) ≤
          ENNReal.ofReal (Real.exp (C * (1 + β ^ 2)) * (N : ℝ)⁻¹)) := by sorry

end SYKLearn
