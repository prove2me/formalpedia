-- Prove2me | Theorems.Thm_PI_CMT_isTr_one
-- name    : PI.CMT.isTr_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:44.676675+00:00
-- url     : https://prove2.me/theorems/d2df01a5-4c09-4c59-9ee1-9caed929fb9a
-- title:
--   CMT: is Tr one
-- statement:
--   The CMT construction uses the is Tr one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMTraceSurjective/IsTrMulConjOfMem.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMTraceSurjective/IsTrMulConjOfMem.lean#L95-L103

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]

theorem PI.CMT.isTr_one
    (hP : ∀ P : Ideal (𝓞 K), P.IsMaximal →
      ∃ θ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ) ∧ θ - t ∉ P) :
    IsTr (1 : 𝓞 K) := by sorry
