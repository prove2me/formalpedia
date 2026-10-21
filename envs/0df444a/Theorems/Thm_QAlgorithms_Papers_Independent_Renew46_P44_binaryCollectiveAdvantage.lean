-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_binaryCollectiveAdvantage
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.binaryCollectiveAdvantage
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:31:46.245973+00:00
-- url     : https://prove2.me/theorems/1631e2ae-0c66-4883-a389-aac10de5898c
-- title:
--   §III.3: binary capacities and strict collective-measurement advantage
-- statement:
--   Let two unit pure signals in a two-dimensional Hilbert space have overlap $\epsilon\in[0,1]$. Their capacity $C$ and single-letter accessible-information supremum $C_1$ are
--
--   $$C=-\sum_{\pm}\frac{1\pm\epsilon}2\log\frac{1\pm\epsilon}2,$$
--
--   $$C_1=\frac12\sum_{\pm}(1\pm\sqrt{1-\epsilon^2})\log(1\pm\sqrt{1-\epsilon^2}).$$
--
--   Use $0\log0=0$. The second value is attained by the uniform prior and a symmetric orthonormal binary Bayes measurement, with error $(1-\sqrt{1-\epsilon^2})/2$. For $0<\epsilon<1$,
--
--   $$C_1<\widetilde C=-\log\frac{1+\epsilon^2}2\le C,\qquad
--   \exists n\ge2:\ C_n>nC_1.$$
--
--   Here $C_n$ allows collective measurements on product-letter words. The final existential property corrects the printed inequality's impossible $n=1$ reading. The $C_1$ formula retains its cited provenance [Lev95], [Osa98].
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 15, §III.3: binary capacities and strict collective-measurement advantage

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.15: exact capacities and strict collective-measurement advantage.
Printed C_n>n C_1 cannot include n=1; changed to existence of n>=2,
as implied by C>C_1 and the regularized limit. C_1 is credited to [Lev95],[Osa98]. -/
theorem binaryCollectiveAdvantage (psi : Bool → Hilbert (Fin 2))
    (hpsi : ∀ b, ‖psi b‖ = 1) (epsilon : ℝ)
    (hoverlap : ‖inner ℂ (psi false) (psi true)‖ = epsilon)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) :
    averageErrorCqCapacity (fun b => TC.rankOne (psi b)) (fun _ => 0) 0 =
      ENNReal.ofReal (binaryCapacityValue epsilon) ∧
    cqInformationBlock (fun b => TC.rankOne (psi b)) 1 =
      ENNReal.ofReal (binaryOneShotValue epsilon) ∧
    (∃ X : DecisionRule (Fin 2), ∃ e : Bool → Hilbert (Fin 2), Orthonormal ℂ e ∧
      X.effect 0 = InnerProductSpace.rankOne ℂ (e false) (e false) ∧
      X.effect 1 = InnerProductSpace.rankOne ℂ (e true) (e true) ∧
      (∀ k : ℕ, 2 ≤ k → X.effect k = 0) ∧
      ‖inner ℂ (e false) (psi false)‖ ^ 2 = (1 + Real.sqrt (1 - epsilon ^ 2)) / 2 ∧
      ‖inner ℂ (e true) (psi true)‖ ^ 2 = (1 + Real.sqrt (1 - epsilon ^ 2)) / 2 ∧
      discreteReceiverInformation (fun b => TC.rankOne (psi b))
        (bernoulliInputLaw (1 / 2) (by norm_num) (by norm_num)) X =
          ENNReal.ofReal (binaryOneShotValue epsilon)) ∧
    (0 < epsilon → epsilon < 1 →
      binaryOneShotValue epsilon < -Real.log ((1 + epsilon ^ 2) / 2) ∧
      ENNReal.ofReal (-Real.log ((1 + epsilon ^ 2) / 2)) ≤
        averageErrorCqCapacity (fun b => TC.rankOne (psi b)) (fun _ => 0) 0 ∧
      ∃ n : ℕ, 2 ≤ n ∧
        (n : ℝ≥0∞) * cqInformationBlock (fun b => TC.rankOne (psi b)) 1 <
          cqInformationBlock (fun b => TC.rankOne (psi b)) n) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
