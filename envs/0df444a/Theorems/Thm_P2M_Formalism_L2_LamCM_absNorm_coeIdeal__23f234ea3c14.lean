-- Prove2me | Theorems.Thm_P2M_Formalism_L2_LamCM_absNorm_coeIdeal__23f234ea3c14
-- name    : P2M_Formalism_L2_LamCM_absNorm_coeIdeal__23f234ea3c14
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:32.63811+00:00
-- url     : https://prove2.me/theorems/0f246c8e-2a48-4817-8826-d63a8ad02a5a
-- title:
--   P2 M Formalism L2 Lam CM abs Norm coe Ideal  23f234ea3c14: P2 M Formalism L2 Lam CM abs Norm coe Ideal  23f234ea3c14
-- statement:
--   The P2 M Formalism L2 Lam CM abs Norm coe Ideal  23f234ea3c14 construction uses the P2 M Formalism L2 Lam CM abs Norm coe Ideal  23f234ea3c14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L144-L145

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
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
open scoped nonZeroDivisors
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]

theorem P2M_Formalism_L2_LamCM_absNorm_coeIdeal__23f234ea3c14 {F : Type} [Field F] [NumberField F] (J : Ideal (𝓞 F)) :
    FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) = (Ideal.absNorm J : ℚ) := by sorry

alias «Formalism».«L2».«LamCM».«absNorm_coeIdeal'» := P2M_Formalism_L2_LamCM_absNorm_coeIdeal__23f234ea3c14
