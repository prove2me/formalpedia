-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_A_BridgeK_coeff_X_mul_derivative__d786c448d91d
-- name    : P2M_Formalism_L2_Th1_A_BridgeK_coeff_X_mul_derivative__d786c448d91d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:17:49.827989+00:00
-- url     : https://prove2.me/theorems/decfefd4-0b25-44f3-b11e-38b6cdb8c20e
-- title:
--   P2 M Formalism L2 Th1 A Bridge K coeff X mul derivative  d786c448d91d: P2 M Formalism L2 Th1 A Bridge K coeff X mul derivative  d786c448d91d
-- statement:
--   The P2 M Formalism L2 Th1 A Bridge K coeff X mul derivative  d786c448d91d construction uses the P2 M Formalism L2 Th1 A Bridge K coeff X mul derivative  d786c448d91d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeK.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeK.lean#L106-L113

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.BridgeK
open Formalism.L2.Th1.CM

theorem P2M_Formalism_L2_Th1_A_BridgeK_coeff_X_mul_derivative__d786c448d91d {K : Type} [Field K] (f : K⟦X⟧) (n : ℕ) :
    coeff n (X * derivative K f) = (n : K) * coeff n f := by sorry

alias «Formalism».«L2».«Th1».«A».«BridgeK».«coeff_X_mul_derivative'» := P2M_Formalism_L2_Th1_A_BridgeK_coeff_X_mul_derivative__d786c448d91d
