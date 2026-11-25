-- Prove2me | Theorems.Thm_PositivityTheory_KReal_extreme
-- name    : PositivityTheory.KReal.extreme
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:18.830407+00:00
-- url     : https://prove2.me/theorems/7e99b333-6a3c-5b20-b608-851878e7f460
-- title:
--   KReal: extreme
-- statement:
--   The KReal construction uses the extreme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreComb.lean#L70-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreComb.lean#L70-L117

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreComb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal

theorem PositivityTheory.KReal.extreme {r s : ℕ} {ν La : Ix r s → ℚ} (hD : Dom ν) :
    (∀ (i : Fin r) (j : Fin s), RootTo ν (.inr j) (.inl i) La →
      (∀ i', i' < i → La (.inl i') = La (.inl i)) → (∀ j', j < j' → La (.inr j') = La (.inr j)) →
      0 < La (.inl i) - La (.inr j) →
      (r : ℚ) + s < 2 * (La (.inl i) - La (.inr j)) + 2 + (rho2 (.inl i : Ix r s) - rho2 (.inr j : Ix r s))) ∧
    (∀ (i : Fin r) (j : Fin s), RootTo ν (.inl i) (.inr j) La →
      (∀ j', j' < j → La (.inr j') = La (.inr j)) → (∀ i', i < i' → La (.inl i') = La (.inl i)) →
      0 < La (.inr j) - La (.inl i) →
      (r : ℚ) + s < 2 * (La (.inr j) - La (.inl i)) + 2 + (rho2 (.inr j : Ix r s) - rho2 (.inl i : Ix r s))) := by sorry
