-- Prove2me | Theorems.Thm_P2M_Formalism_IndefR_Eqv_natCast_lt_inf__24812f2382ad
-- name    : P2M_Formalism_IndefR_Eqv_natCast_lt_inf__24812f2382ad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:23.3278+00:00
-- url     : https://prove2.me/theorems/41048d23-fb8d-440f-9c08-bfe1a4841ab2
-- title:
--   P2 M Formalism Indef R Eqv nat Cast lt inf  24812f2382ad: P2 M Formalism Indef R Eqv nat Cast lt inf  24812f2382ad
-- statement:
--   The P2 M Formalism Indef R Eqv nat Cast lt inf  24812f2382ad construction uses the P2 M Formalism Indef R Eqv nat Cast lt inf  24812f2382ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L11-L12

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem P2M_Formalism_IndefR_Eqv_natCast_lt_inf__24812f2382ad (m : ℕ) : (m : WithTop ℕ∞) < ∞ := by sorry

alias «Formalism».«IndefR».«Eqv».«natCast_lt_inf'» := P2M_Formalism_IndefR_Eqv_natCast_lt_inf__24812f2382ad
