-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_sum_comm
-- name    : PositivityTheory.Rg.Cz.SpecA.sum_comm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:47.690178+00:00
-- url     : https://prove2.me/theorems/08641116-b612-419f-bb29-2656e2536371
-- title:
--   Spec A: sum comm
-- statement:
--   The Spec A construction uses the sum comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L66-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L66-L103

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

theorem PositivityTheory.Rg.Cz.SpecA.sum_comm {R : Type*} [CommRing R] [Algebra ℂ R] (A B : R) (α β : ℂ) (La Lb : List ℕ)
    (hA : (La.map fun a : ℕ => A - algebraMap ℂ R (α + a)).prod = 0)
    (hB : (Lb.map fun b : ℕ => B - algebraMap ℂ R (β + b)).prod = 0) :
    ((La.flatMap fun a => Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod = 0 := by sorry
