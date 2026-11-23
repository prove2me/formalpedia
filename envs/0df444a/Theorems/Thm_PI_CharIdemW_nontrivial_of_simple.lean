-- Prove2me | Theorems.Thm_PI_CharIdemW_nontrivial_of_simple
-- name    : PI.CharIdemW.nontrivial_of_simple
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:10.178425+00:00
-- url     : https://prove2.me/theorems/570e10aa-36be-4868-9f7c-ab732fd58ded
-- title:
--   Char Idem W: nontrivial of simple
-- statement:
--   The Char Idem W construction uses the nontrivial of simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L53-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L53-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]

theorem PI.CharIdemW.nontrivial_of_simple (W : FDRep ℂ G) [Simple W] : Nontrivial W := by sorry
