-- Prove2me | Theorems.Thm_PI_CharIdemW_comm_of_class
-- name    : PI.CharIdemW.comm_of_class
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:09.715961+00:00
-- url     : https://prove2.me/theorems/bd556a02-cb28-4a37-b669-befe28fcbef3
-- title:
--   Char Idem W: comm of class
-- statement:
--   The Char Idem W construction uses the comm of class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L25-L31

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

theorem PI.CharIdemW.comm_of_class (W : FDRep ℂ G) (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h : G) : W.ρ h * (∑ g : G, f g • W.ρ g) = (∑ g : G, f g • W.ρ g) * W.ρ h := by sorry
