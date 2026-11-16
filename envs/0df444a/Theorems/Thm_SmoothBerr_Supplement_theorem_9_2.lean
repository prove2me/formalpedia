-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_9_2
-- name    : SmoothBerr.Supplement.theorem_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:57:17.429197+00:00
-- url     : https://prove2.me/theorems/de2a4270-a638-4797-92cb-dd6390c7ce9a
-- title:
--   Theorem 9.2 — randomized lower bounds for backward error: $(e^{-1}-o(1))/\varepsilon$ (symmetric), $(e^{-1}-o(1))/\sqrt\varepsilon$ (psd)
-- statement:
--   1. **Symmetric systems.** For every $\delta>0$ there is $\varepsilon_0>0$ such that for all $0<\varepsilon<\varepsilon_0$ and all $t$: if for every $n$ there is a randomized adaptive matvec algorithm with $t$ matvecs that, for every symmetric invertible $A\in\mathbb R^{n\times n}$ and every $b$, returns $\tilde x$ with $\mathrm{berr}(A,b,\tilde x)\le\varepsilon$ with probability at least $2/3$, then
--   $$
--   t\ \ge\ \frac{e^{-1}-\delta}{\varepsilon}.
--   $$
--   2. **Positive definite systems.** The same holds with "symmetric invertible" replaced by "positive definite", with the bound
--   $$
--   t\ \ge\ \frac{e^{-1}-\delta}{\sqrt\varepsilon}.
--   $$
--
--   The bounds show that the deterministic $O(1/\varepsilon)$ algorithm of Theorem 2.3 is optimal up to the constant even among randomized algorithms, and that for psd systems the $O(1/\sqrt\varepsilon)$ rate of Krylov methods cannot be improved.
--
--   **Formalization Note** The probability is over the algorithm's seed. The algorithm may depend on $n$; "any symmetric linear system" ranges over all dimensions. Success is required only on invertible systems (positive definite in the psd case).
--
--   Differences from the source:
--   - reading: t ≥ (e⁻¹ − o(1))/ε, little-oh shrinking as ε grows small (and /√ε for psd) → ∀ δ > 0, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), the bound (e⁻¹ − δ)/ε ≤ t (resp. (e⁻¹ − δ)/√ε ≤ t); reason: the printed limit as ε → 0
--   - generalization: an algorithm which can solve any symmetric (resp. psd) linear system → for every n some algorithm (allowed to depend on n) succeeds on every symmetric invertible (resp. positive definite) A ∈ ℝ^{n×n} and every b; reason: the hypothesis is weaker, so the theorem is stronger; the proof's hard instances (cond(A) ≤ κ) are invertible
--   - reading: a possibly randomized and possibly adaptive matvec algorithm → RandMatvecAlg: seed from a probability law μ, t adaptive single matvecs v ↦ Av, queries and output measurable jointly in the seed and the answers; reason: the measurability that a success probability presupposes; Aᵀv = Av on symmetric inputs
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 9.2, p.24

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_BerrLe
import Definitions.Def_SmoothBerr_Supplement_RandMatvecAlg

open MeasureTheory Matrix
open scoped ENNReal

namespace SmoothBerr.Supplement

/-- **Theorem 9.2 (Symmetric and psd lower bounds for backward error)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 9.2, p.24).

Every (possibly randomized and possibly adaptive) matvec algorithm which can solve any symmetric
linear system to backward error at most `ε` with probability at least `2/3` must use
`t ≥ (e⁻¹ − o(1))/ε` matvecs, where the little-oh shrinks as `ε` grows small. For psd systems
the rate shrinks to `t ≥ (e⁻¹ − o(1))/√ε`.

**Formalization Note**
1. `o(1)` is a limit as `ε → 0`: for every `δ > 0` there is `ε₀ > 0` such that for every
   `ε ∈ (0, ε₀)` and `t` the implication holds with bound `(e⁻¹ − δ)/ε` (resp. `(e⁻¹ − δ)/√ε`).
2. "Any symmetric linear system" ranges over every dimension: the hypothesis is that for every
   `n` some randomized algorithm with `t` matvecs (`RandMatvecAlg`, seed law `μ`; it may depend
   on `n`) returns, for every symmetric invertible (resp. positive definite) `A` and every `b`,
   a vector with backward error `≤ ε` (`BerrLe`) with probability `≥ 2/3`.
3. Success is required only on invertible systems; psd and invertible is `Matrix.PosDef`. -/
theorem theorem_9_2 :
    (∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ t : ℕ,
      (∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ ∧ ∃ alg : RandMatvecAlg n t Ω,
          ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm → IsUnit A.det → ∀ b : Fin n → ℝ,
            (2 / 3 : ℝ≥0∞) ≤ μ {ω | BerrLe A b (alg.run A b ω) ε}) →
      (Real.exp (-1) - δ) / ε ≤ t) ∧
    (∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ t : ℕ,
      (∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ ∧ ∃ alg : RandMatvecAlg n t Ω,
          ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef → ∀ b : Fin n → ℝ,
            (2 / 3 : ℝ≥0∞) ≤ μ {ω | BerrLe A b (alg.run A b ω) ε}) →
      (Real.exp (-1) - δ) / Real.sqrt ε ≤ t) := by sorry

end SmoothBerr.Supplement
