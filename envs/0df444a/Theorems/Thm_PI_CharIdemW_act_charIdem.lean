-- Prove2me | Theorems.Thm_PI_CharIdemW_act_charIdem
-- name    : PI.CharIdemW.act_charIdem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:57.413344+00:00
-- url     : https://prove2.me/theorems/e6ac71f3-4a03-4bac-beb9-df6ca3a72250
-- title:
--   Char Idem W: act char Idem
-- statement:
--   The Char Idem W construction uses the act char Idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L19-L23

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

theorem PI.CharIdemW.act_charIdem (V W : FDRep ℂ G) :
    act W (charIdem V) = ∑ g : G,
      (((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹) • W.ρ g := by sorry
