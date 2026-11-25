-- Prove2me | Theorems.Thm_PI_EagonNorthcottZ_KK
-- name    : PI.EagonNorthcottZ.KK
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:52.367852+00:00
-- url     : https://prove2.me/theorems/cd53f2d7-5b83-5002-9358-ebff964cf932
-- title:
--   Eagon Northcott Z: KK
-- statement:
--   The Eagon Northcott Z construction uses the KK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/AugmentationDegreeZero.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/AugmentationDegreeZero.lean#L14-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_YHom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_AugmentationDegreeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EagonNorthcottZ
open MvPolynomial Finset

theorem PI.EagonNorthcottZ.KK {D : ℕ} (t u : Fin D → P D) (ω : W D) (J : Finset (Fin D)) :
    K t (K u ω) J = ∑ i ∈ Jᶜ, ∑ l ∈ Jᶜ, (if l = i then 0 else
      (sgn i J : P D) * (sgn l (insert i J) : P D) * (t i * u l) * ω (insert l (insert i J))) := by sorry
