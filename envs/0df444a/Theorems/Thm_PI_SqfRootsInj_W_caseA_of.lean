-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_caseA_of
-- name    : PI.SqfRootsInj.W.caseA_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:28:04.996278+00:00
-- url     : https://prove2.me/theorems/a3dcd15e-f4d9-5c6d-9051-c37f964a6533
-- title:
--   W: case A of
-- statement:
--   The W construction uses the case A of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L91-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L91-L150

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]

theorem PI.SqfRootsInj.W.caseA_of {r ℓ : ℕ} (hℓ : ℓ.Prime) {f : (ZMod g)[X]} (hf : IsLab g r f)
    {x y : Fbar g} (hx : x ∈ rootsBar f) (hy : y ∈ rootsBar f) (hxy : x ≠ y)
    (hp : primeToPart ℓ x = primeToPart ℓ y)
    (heq : minpoly (ZMod g) x = minpoly (ZMod g) y) :
    CaseA g r ℓ f := by sorry
