-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_A_Wp_isDer_dL__14cb087f2915
-- name    : P2M_Formalism_L2_Th1_A_Wp_isDer_dL__14cb087f2915
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:59.429104+00:00
-- url     : https://prove2.me/theorems/1930a429-0603-45d0-b311-e20e8d01373d
-- title:
--   P2 M Formalism L2 Th1 A Wp is Der d L  14cb087f2915: P2 M Formalism L2 Th1 A Wp is Der d L  14cb087f2915
-- statement:
--   The P2 M Formalism L2 Th1 A Wp is Der d L  14cb087f2915 construction uses the P2 M Formalism L2 Th1 A Wp is Der d L  14cb087f2915 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ConstCurveDL.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ConstCurveDL.lean#L34-L34

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ConstCurveDL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Wp
variable {K : Type u} [Field K]

theorem P2M_Formalism_L2_Th1_A_Wp_isDer_dL__14cb087f2915 : IsDer (dL : LaurentSeries K → LaurentSeries K) := by sorry

alias «Formalism».«L2».«Th1».«A».«Wp».«isDer_dL'» := P2M_Formalism_L2_Th1_A_Wp_isDer_dL__14cb087f2915
