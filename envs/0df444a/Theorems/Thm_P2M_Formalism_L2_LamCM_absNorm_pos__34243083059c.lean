-- Prove2me | Theorems.Thm_P2M_Formalism_L2_LamCM_absNorm_pos__34243083059c
-- name    : P2M_Formalism_L2_LamCM_absNorm_pos__34243083059c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:18.246802+00:00
-- url     : https://prove2.me/theorems/c65d955d-1d45-4140-9e4f-3ee398297d90
-- title:
--   P2 M Formalism L2 Lam CM abs Norm pos  34243083059c: P2 M Formalism L2 Lam CM abs Norm pos  34243083059c
-- statement:
--   The P2 M Formalism L2 Lam CM abs Norm pos  34243083059c construction uses the P2 M Formalism L2 Lam CM abs Norm pos  34243083059c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L14-L18

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
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
variable {K : Type} [Field K] [NumberField K]

theorem P2M_Formalism_L2_LamCM_absNorm_pos__34243083059c {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (0 : ℝ) < ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by sorry

alias «Formalism».«L2».«LamCM».«absNorm_pos'» := P2M_Formalism_L2_LamCM_absNorm_pos__34243083059c
