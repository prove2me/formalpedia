-- Prove2me | Theorems.Thm_P2M_RH_PI_CharIdemW_act_single_f1540b4be5967fc7
-- name    : P2M_RH_PI_CharIdemW_act_single_f1540b4be5967fc7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:10.761547+00:00
-- url     : https://prove2.me/theorems/70241dab-1159-4e21-8f8d-506bcdfdc638
-- title:
--   P2 M RH PI Char Idem W act single f1540b4be5967fc7: P2 M RH PI Char Idem W act single f1540b4be5967fc7
-- statement:
--   The P2 M RH PI Char Idem W act single f1540b4be5967fc7 construction uses the P2 M RH PI Char Idem W act single f1540b4be5967fc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/CoeffMulCharIdem.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/CoeffMulCharIdem.lean#L14-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Central
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_CoeffMulCharIdem
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

theorem P2M_RH_PI_CharIdemW_act_single_f1540b4be5967fc7 (W : FDRep ℂ G) (g : G) (r : ℂ) :
    act W (MonoidAlgebra.single g r) = r • W.ρ g := by sorry

alias «PI».«CharIdemW».«act_single» := P2M_RH_PI_CharIdemW_act_single_f1540b4be5967fc7
