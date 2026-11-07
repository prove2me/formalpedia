-- Prove2me | Theorems.Thm_SmoothBerr_theorem_4_1
-- name    : SmoothBerr.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:13.923278+00:00
-- url     : https://prove2.me/theorems/830738fa-f0ff-4f68-b901-eacbcf49b461
-- title:
--   Theorem 4.1 — smoothed lower bound on the Gaussian instance: $\Omega(n)$ matvecs
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ have iid $\mathcal N(0,1)$ entries, let $\Delta\in\mathbb R^{n\times n}$ be independent of $A$ with $\|\Delta\|_2\le\sqrt n/3$ almost surely, and set $\hat A:=A+\Delta$. There are universal constants $p\in(0,1)$ and $C>0$ such that the following holds. If a randomized algorithm with matvec access to $\hat A$ and $\hat A^\top$, using $t$ matvecs, outputs for every right-hand side $b\ne0$ a vector $\tilde x$ with
--   $$
--   \|\tilde x-\hat A^{-1}b\|_2\le\frac1{20}\|\hat A^{-1}b\|_2\qquad\text{with probability}\ \ge p,
--   $$
--   then $t\ge Cn$.
--
--   Even when the matrix is a perturbed Gaussian matrix and the algorithm may use both $\hat A$ and $\hat A^\top$, a constant-accuracy solution with constant probability costs $\Omega(n)$ matvecs. Scaling by $\Theta(1/\sqrt n)$ turns this into the goal, Theorem 2.1.
--
--   **Formalization Note** The probability is over the seed, $A$ and $\Delta$ jointly (independent). A singular $\hat A$ counts as a success (a null event here).
--
--   Differences from the source:
--   - generalization: any algorithm with matvec access to Â and Âᵀ → a randomized adaptive paired matvec algorithm with exactly t steps, each returning both Âᵀu and Âv; reason: each matvec with Â (or Âᵀ) is part of one paired step, and an algorithm with fewer steps ignores its last answers; a lower bound against the larger class specializes to the printed one
--   - reading: output x̃ with the bound "with prob. ≥ p" (b is arbitrary, p.5) → for every b ≠ 0, probability ≥ p over the seed, A and Δ; reason: the proof runs the solver on Gaussian right-hand sides (p.12), so the guarantee is required for every b
--   - generalization: success ‖x̃ − Â⁻¹b‖₂ ≤ (1/20)‖Â⁻¹b‖₂ required for every b → success required only for b ≠ 0, and a singular Â counts as a success (Solves); reason: the hypothesis is weaker, so the theorem is stronger; it specializes to the printed statement
--   - reading: a randomized algorithm succeeding "with probability" → a seed ω drawn from a probability law μ on a measurable space Ω, independent of the matrices; queries and output measurable jointly in the seed and the answers; reason: the measurability that a probability of success presupposes; the seed is the algorithm's own randomness
--   - generalization: an algorithm that takes b (measurable in b, implicitly) → no measurability in the input b: query and output may depend on b arbitrarily (PairedMatvecAlg requires measurability only in the seed and the answers, for each fixed b); reason: the hypothesis is a per-b guarantee, so the Lean class contains every measurable algorithm and the bound specializes to the printed one; the proof averages over random right-hand sides, which can be taken from the finite Rademacher set {±1}ⁿ (Hutchinson bounds E[Y] = ‖Â⁻¹‖_F², E[Y²] ≤ 3‖Â⁻¹‖_F⁴ hold for it too), where measurability in b is automatic
--   - encoding: a universal constant p ∈ (0,1) such that ... requires Ω(n) matvecs → ∃ p ∈ (0,1), ∃ C > 0, chosen before n, ν, t and the algorithm, with C·n ≤ t; reason: §3, p.4: Ω hides a universal constant
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 4.1, p.5

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SmoothBerr_PairedMatvecAlg
import Definitions.Def_SmoothBerr_Solves

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **Theorem 4.1 (Smoothed lower bound)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 4.1, p.5).

Let `A ∈ ℝ^{n×n}` have iid `N(0,1)` entries, let `Δ ∈ ℝ^{n×n}` be independent of `A` with
`‖Δ‖₂ ≤ √n/3` almost surely, and set `Â := A + Δ`. There is a universal constant `p ∈ (0,1)` such
that any algorithm with matvec access to `Â` and `Âᵀ` requires `Ω(n)` matvecs to output, for
every right-hand side `b`, a vector `x̃` with `‖x̃ − Â⁻¹b‖₂ ≤ (1/20)‖Â⁻¹b‖₂` with probability at
least `p`.

**Formalization Note** "Requires `Ω(n)` matvecs": there are universal `p ∈ (0,1)` and `C > 0`,
chosen before `n`, such that every randomized adaptive paired matvec algorithm with `t` steps
(input `b`, seed law `μ` independent of `(A, Δ)`) that succeeds with probability at least `p` for
every `b ≠ 0` has `t ≥ C n`. The probability is over `μ ⊗ gaussianMatrix n n ⊗ ν`. Success is
`Solves`: the forward-error bound, or `Â` singular (a null event here). A paired step gives both
`Âᵀu` and `Âv`, so `t` paired steps cover any algorithm with at most `t` matvecs with `Â` and
`Âᵀ`. -/
theorem theorem_4_1 :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧
      ∀ (n t : ℕ) (ν : Measure (Fin n → Fin n → ℝ)) [IsProbabilityMeasure ν],
        (∀ᵐ Δ ∂ν, specNorm (Matrix.of Δ) ≤ Real.sqrt n / 3) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (alg : PairedMatvecAlg n t (Fin n → ℝ) Ω (Fin n → ℝ)),
          (∀ b : Fin n → ℝ, b ≠ 0 →
            ENNReal.ofReal p ≤ (μ.prod ((gaussianMatrix n n).prod ν))
              {q | Solves (Matrix.of q.2.1 + Matrix.of q.2.2) b
                (alg.run (Matrix.of q.2.1 + Matrix.of q.2.2) b q.1)}) →
          C * n ≤ t := by sorry

end SmoothBerr
