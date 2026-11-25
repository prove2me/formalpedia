-- Prove2me | Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_pow__280537c55445
-- name    : P2M_Formalism_L2_LamCM_IsLocGen_pow__280537c55445
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:08.505778+00:00
-- url     : https://prove2.me/theorems/2abd6e86-460e-4f19-a439-52e4d9192597
-- title:
--   P2 M Formalism L2 Lam CM Is Loc Gen pow  280537c55445: P2 M Formalism L2 Lam CM Is Loc Gen pow  280537c55445
-- statement:
--   The P2 M Formalism L2 Lam CM Is Loc Gen pow  280537c55445 construction uses the P2 M Formalism L2 Lam CM Is Loc Gen pow  280537c55445 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L390-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L390-L394

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

theorem P2M_Formalism_L2_LamCM_IsLocGen_pow__280537c55445 {a : K} {I : FractionalIdeal (𝓞 K)⁰ K} (ha : IsLocGen p a I) (k : ℕ) :
    IsLocGen p (a ^ k) (I ^ k) := by sorry

alias «Formalism».«L2».«LamCM».«IsLocGen».«pow'» := P2M_Formalism_L2_LamCM_IsLocGen_pow__280537c55445
