-- Prove2me | Theorems.Thm_PI_FiltrationLength_ell_stepF
-- name    : PI.FiltrationLength.ell_stepF
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:26.659621+00:00
-- url     : https://prove2.me/theorems/e28ccb46-e4eb-4582-8d36-b59b08d5719d
-- title:
--   Filtration Length: ell step F
-- statement:
--   The Filtration Length construction uses the ell step F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiltrationLength/FiltLenFMain.lean#L12-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiltrationLength/FiltLenFMain.lean#L12-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FiltLen
import Definitions.Def_Formalism_PeriodIntegrals_FiltLenF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_LengthQuotLeOfKerLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_FiltLenFMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FiltrationLength
open Submodule
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem PI.FiltrationLength.ell_stepF {V : Type} [AddCommGroup V] [Module R V]
    (M N Fk Fk1 : Submodule R W) (ψ : ↥Fk →ₗ[R] V) (P Q : Submodule R V) (hNM : N ≤ M)
    (hinj : ∀ x : ↥Fk, ψ x = 0 → (x : W) ∈ Fk1)
    (hP : (M.comap Fk.subtype).map ψ ≤ P) (hQ : Q ≤ (N.comap Fk.subtype).map ψ) :
    ell (M ⊓ Fk) ((N ⊓ Fk) ⊔ (M ⊓ Fk1)) ≤ Module.length R (↥P ⧸ Q.comap P.subtype) := by sorry
