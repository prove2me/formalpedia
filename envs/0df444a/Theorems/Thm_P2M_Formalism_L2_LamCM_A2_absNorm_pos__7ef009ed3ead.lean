-- Prove2me | Theorems.Thm_P2M_Formalism_L2_LamCM_A2_absNorm_pos__7ef009ed3ead
-- name    : P2M_Formalism_L2_LamCM_A2_absNorm_pos__7ef009ed3ead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:09.414831+00:00
-- url     : https://prove2.me/theorems/38a27862-13cf-4da0-8509-d2da875e49b8
-- title:
--   P2 M Formalism L2 Lam CM A2 abs Norm pos  7ef009ed3ead: P2 M Formalism L2 Lam CM A2 abs Norm pos  7ef009ed3ead
-- statement:
--   The P2 M Formalism L2 Lam CM A2 abs Norm pos  7ef009ed3ead construction uses the P2 M Formalism L2 Lam CM A2 abs Norm pos  7ef009ed3ead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L14-L15

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]

theorem P2M_Formalism_L2_LamCM_A2_absNorm_pos__7ef009ed3ead {I : FractionalIdeal (𝓞 K)⁰ K} (h : I ≠ 0) : 0 < FractionalIdeal.absNorm I := by sorry

alias «Formalism».«L2».«LamCM».«A2».«absNorm_pos'» := P2M_Formalism_L2_LamCM_A2_absNorm_pos__7ef009ed3ead
