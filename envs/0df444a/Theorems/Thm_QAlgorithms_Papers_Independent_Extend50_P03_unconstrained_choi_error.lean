-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_unconstrained_choi_error
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.unconstrained_choi_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:56:01.237024+00:00
-- url     : https://prove2.me/theorems/126f28c1-7ae5-471a-9e8e-ac41c0198592
-- title:
--   §4.3: fully Haar-random encoders without charge conservation
-- statement:
--   Let $k\le n$ and $t\le n$, and append any fixed normalized pure $(n-k)$-qubit ancilla independent of the encoder. Draw $U$ from probability Haar on $\mathrm{SU}(2^n)$, and erase any specified $t$ physical wires. Let $\varepsilon_{\rm Choi}$ be the optimized normalized-EPR error using root fidelity. Set $\Delta=n-k-4t\ge0$. There are absolute $c>0$ and an integer $\Delta_0$ such that, uniformly over the sizes, ancilla and erased set, for $\Delta\ge\Delta_0$,
--
--   $$\mathbb E\varepsilon_{\rm Choi}\le e^{-c\Delta}.$$
--
--   The expectation is integrable. This asserts decay as $\Delta\to\infty$, without asserting decay in $n$ for bounded $\Delta$.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 12, §4.3: fully Haar-random encoders without charge conservation

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Section 4.3, PDF p.12: fully SU(2^n)-Haar encoders, fixed arbitrary pure
ancilla. Delta is n-k-4t, not n; exponential decay is asserted as Delta grows. -/
theorem unconstrained_choi_error :
    ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, ∀ n k t : ℕ, ∀ h : k ≤ n,
      t ≤ n → 4*t ≤ n-k → D ≤ n-k-4*t →
      ∀ psi : EuclideanSpace ℂ (Qubits (n-k)), IsState psi →
      ∀ mu : Measure ((Matrix.unitaryGroup (Qubits n) ℂ)), SpecialHaar n mu →
      ∀ S : Finset (Fin n), S.card = t →
      let error := fun U => optimizedCodeError false (retain Sᶜ ∘ pureEncoder h psi U)
      Integrable error mu ∧ (∫ U, error U ∂mu) ≤ Real.exp (-c * (n-k-4*t : ℕ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
