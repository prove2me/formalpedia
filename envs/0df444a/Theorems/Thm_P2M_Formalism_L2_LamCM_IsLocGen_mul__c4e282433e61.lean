-- Prove2me | Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_mul__c4e282433e61
-- name    : P2M_Formalism_L2_LamCM_IsLocGen_mul__c4e282433e61
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:25.894542+00:00
-- url     : https://prove2.me/theorems/4db3a0ef-ce47-43e7-bdd3-9e485e3f3bc8
-- title:
--   P2 M Formalism L2 Lam CM Is Loc Gen mul  c4e282433e61: P2 M Formalism L2 Lam CM Is Loc Gen mul  c4e282433e61
-- statement:
--   The P2 M Formalism L2 Lam CM Is Loc Gen mul  c4e282433e61 construction uses the P2 M Formalism L2 Lam CM Is Loc Gen mul  c4e282433e61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L380-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L380-L388

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
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
variable {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}

theorem P2M_Formalism_L2_LamCM_IsLocGen_mul__c4e282433e61 {a b : K} {I J : FractionalIdeal (𝓞 K)⁰ K}
    (ha : IsLocGen p a I) (hb : IsLocGen p b J) (hI : I ≠ 0) (hJ : J ≠ 0) : IsLocGen p (a * b) (I * J) := by sorry

alias «Formalism».«L2».«LamCM».«IsLocGen».«mul'» := P2M_Formalism_L2_LamCM_IsLocGen_mul__c4e282433e61
