-- Prove2me | Theorems.Thm_P2M_Formalism_L2_LamCM_A2_absNorm_anti__8418fc33d666
-- name    : P2M_Formalism_L2_LamCM_A2_absNorm_anti__8418fc33d666
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:16.373716+00:00
-- url     : https://prove2.me/theorems/aff790ec-6ddb-4676-aa3b-1d835170212a
-- title:
--   P2 M Formalism L2 Lam CM A2 abs Norm anti  8418fc33d666: P2 M Formalism L2 Lam CM A2 abs Norm anti  8418fc33d666
-- statement:
--   The P2 M Formalism L2 Lam CM A2 abs Norm anti  8418fc33d666 construction uses the P2 M Formalism L2 Lam CM A2 abs Norm anti  8418fc33d666 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L17-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L17-L41

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

theorem P2M_Formalism_L2_LamCM_A2_absNorm_anti__8418fc33d666 {I J : FractionalIdeal (𝓞 K)⁰ K} (hIJ : I ≤ J) (hI : I ≠ 0) :
    FractionalIdeal.absNorm J ≤ FractionalIdeal.absNorm I := by sorry

alias «Formalism».«L2».«LamCM».«A2».«absNorm_anti'» := P2M_Formalism_L2_LamCM_A2_absNorm_anti__8418fc33d666
