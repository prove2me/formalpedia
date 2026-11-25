-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_A_ZSer_iSerSpec__ff57dfa23ee4
-- name    : P2M_Formalism_L2_Th1_A_ZSer_iSerSpec__ff57dfa23ee4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:48.852889+00:00
-- url     : https://prove2.me/theorems/069c1eef-1d3c-4164-98fb-612130748d93
-- title:
--   P2 M Formalism L2 Th1 A ZSer i Ser Spec  ff57dfa23ee4: P2 M Formalism L2 Th1 A ZSer i Ser Spec  ff57dfa23ee4
-- statement:
--   The P2 M Formalism L2 Th1 A ZSer i Ser Spec  ff57dfa23ee4 construction uses the P2 M Formalism L2 Th1 A ZSer i Ser Spec  ff57dfa23ee4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/SubstPairSubst.lean#L160-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/SubstPairSubst.lean#L160-L161

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.ZSer
local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) (fgl W)
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem P2M_Formalism_L2_Th1_A_ZSer_iSerSpec__ff57dfa23ee4 : ISerSpec.{u} := by sorry

alias «Formalism».«L2».«Th1».«A».«ZSer».«iSerSpec'» := P2M_Formalism_L2_Th1_A_ZSer_iSerSpec__ff57dfa23ee4
