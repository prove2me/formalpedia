-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_holevoMeasurementBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.holevoMeasurementBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:01:48.925819+00:00
-- url     : https://prove2.me/theorems/851cfa1e-4b58-46a6-8c08-ae5da51280d0
-- title:
--   Equations (47)–(50): Holevo measurement bound
-- statement:
--   Let $\mathcal E=\{\pi_j,\rho_j\}$ be any finite ensemble of normalized PSD states, with nonnegative weights summing to one and average $\bar\rho=\sum_j\pi_j\rho_j$. For every finite POVM $\mathcal M=\{E_b\}$, set $p_j(b)=\operatorname{Tr}(E_b\rho_j)$ and $p(b)=\operatorname{Tr}(E_b\bar\rho)$. With Shannon entropy $H_{\rm Sh}$ in nats,
--   $$I(\mathcal E,\mathcal M):=H_{\rm Sh}(p)-\sum_j\pi_jH_{\rm Sh}(p_j)\le\chi(\mathcal E):=S(\bar\rho)-\sum_j\pi_jS(\rho_j)=\sum_{j:\pi_j>0}\pi_jH(\rho_j,\bar\rho).$$
--   Zero probabilities use the entropy convention $0\log0=0$. This is the pointwise Holevo measurement bound, including singular ensembles.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 17, Equations (47)–(50): Holevo measurement bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P51

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakethird100.P51

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact interfaces from the frozen accepted library; no local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy marginalAB channelAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Gap48.P33 (measurementInformation)

section Statements

variable {A B C D J K O : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype J] [Fintype K] [Fintype O]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq J] [DecidableEq K] [DecidableEq O]

/-- Equations (47)–(50), PDF pp.17–18: the Holevo bound for every POVM, together
with its relative-entropy expression; only active labels enter that expression. -/
theorem holevoMeasurementBound [Nonempty A] [Nonempty J] [Nonempty O] (w : J → ℝ) (hw : IsLaw w)
    (rho : J → Mat A) (hr : ∀ j, IsDensityMatrix (rho j)) (E : O → Mat A) (hE : IsPOVM E) :
    (Real.log 2 * measurementInformation w rho E) ≤ holevo w rho ∧
      holevo w rho = ∑ j, if 0 < w j then w j * (relativeEntropy (rho j) (average w rho)).toReal else 0 := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
