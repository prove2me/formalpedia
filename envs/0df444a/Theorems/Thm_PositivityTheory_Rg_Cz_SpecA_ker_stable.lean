-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_ker_stable
-- name    : PositivityTheory.Rg.Cz.SpecA.ker_stable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:47.250905+00:00
-- url     : https://prove2.me/theorems/14d3b244-a1a7-4078-8c1d-d9b87c0b9501
-- title:
--   Spec A: ker stable
-- statement:
--   The Spec A construction uses the ker stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L163-L167

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

theorem PositivityTheory.Rg.Cz.SpecA.ker_stable {V : Type} [AddCommGroup V] [Module ℂ V] (Y X : Module.End ℂ V) (h : Commute Y X) :
    ∀ w ∈ LinearMap.ker Y, X w ∈ LinearMap.ker Y := by sorry
