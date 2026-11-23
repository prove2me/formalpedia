-- Prove2me | Theorems.Thm_P2M_Formalism_L2_LamCM_spanSingleton_ne_zero__ef0616425764
-- name    : P2M_Formalism_L2_LamCM_spanSingleton_ne_zero__ef0616425764
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:16.735101+00:00
-- url     : https://prove2.me/theorems/3cd4ac6c-d482-4b19-9106-ba374b0d05ad
-- title:
--   P2 M Formalism L2 Lam CM span Singleton ne zero  ef0616425764: P2 M Formalism L2 Lam CM span Singleton ne zero  ef0616425764
-- statement:
--   The P2 M Formalism L2 Lam CM span Singleton ne zero  ef0616425764 construction uses the P2 M Formalism L2 Lam CM span Singleton ne zero  ef0616425764 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L29-L30

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

theorem P2M_Formalism_L2_LamCM_spanSingleton_ne_zero__ef0616425764 {x : K} (hx : x ≠ 0) : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by sorry

alias «Formalism».«L2».«LamCM».«spanSingleton_ne_zero'» := P2M_Formalism_L2_LamCM_spanSingleton_ne_zero__ef0616425764
