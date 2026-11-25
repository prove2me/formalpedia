-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_pm_eAt
-- name    : PositivityTheory.Rg.Cz.TensorGLSums.pm_eAt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:33.664954+00:00
-- url     : https://prove2.me/theorems/2f62de40-dcb7-4093-9f42-2ed3e7235404
-- title:
--   Tensor GLSums: pm e At
-- statement:
--   The Tensor GLSums construction uses the pm e At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L88-L93

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TensorGLSums
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TensorGLSums.pm_eAt (σ : Equiv.Perm P) (p : P) (a b : Fin n) :
    (pm σ * eAt p a b : Module.End ℂ (TV n M P)) = eAt (σ p) a b * pm σ := by sorry
