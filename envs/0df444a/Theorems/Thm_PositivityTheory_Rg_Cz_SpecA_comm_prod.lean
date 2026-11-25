-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_comm_prod
-- name    : PositivityTheory.Rg.Cz.SpecA.comm_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:20.671574+00:00
-- url     : https://prove2.me/theorems/9450fd1d-622f-425e-b888-37fb57fdd0a9
-- title:
--   Spec A: comm prod
-- statement:
--   The Spec A construction uses the comm prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L169-L173

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

theorem PositivityTheory.Rg.Cz.SpecA.comm_prod {V : Type} [AddCommGroup V] [Module ℂ V] (A X : Module.End ℂ V) (h : Commute A X)
    {ι : Type} (g : ι → ℂ) (L : List ι) : Commute (L.map fun c => A - algebraMap ℂ _ (g c)).prod X := by sorry
