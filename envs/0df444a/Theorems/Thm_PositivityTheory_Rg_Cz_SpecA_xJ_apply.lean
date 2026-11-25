-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_xJ_apply
-- name    : PositivityTheory.Rg.Cz.SpecA.xJ_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:10.914457+00:00
-- url     : https://prove2.me/theorems/86adb8d6-a997-5e39-b1e8-1b85af848442
-- title:
--   Spec A: x J apply
-- statement:
--   The Spec A construction uses the x J apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L133-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L133-L143

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}

theorem PositivityTheory.Rg.Cz.SpecA.xJ_apply {m : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m)
    (f : TV n M (Fin m)) (I : Fin m → Fin n) :
    xJ E j f I = ∑ a, E a (I j) (f (Function.update I j a)) +
      ∑ i ∈ Finset.univ.filter (· < j), f (I ∘ Equiv.swap i j) := by sorry
