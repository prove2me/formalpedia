-- Prove2me | Theorems.Thm_PI_InvIdealIdxPiWork_map_mul_inv
-- name    : PI.InvIdealIdxPiWork.map_mul_inv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:12.325312+00:00
-- url     : https://prove2.me/theorems/5ad22a4a-af56-5a47-9dcf-14dbfebd4479
-- title:
--   Inv Ideal Idx Pi Work: map mul inv
-- statement:
--   The Inv Ideal Idx Pi Work construction uses the map mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L51-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L51-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]

theorem PI.InvIdealIdxPiWork.map_mul_inv (J K : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (a : 𝓞 E) (hK : Ideal.span {a} = J * K) :
    ((((J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
        Submodule (𝓞 E) E).toAddSubgroup).map (AddMonoidHom.mulLeft (algebraMap (𝓞 E) E a)) =
      idS K := by sorry
