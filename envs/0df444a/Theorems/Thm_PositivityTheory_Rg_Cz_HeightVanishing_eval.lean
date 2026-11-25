-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_eval
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:20.776802+00:00
-- url     : https://prove2.me/theorems/bcee020e-def9-4b0f-88ea-c269297af03d
-- title:
--   Height Vanishing: eval
-- statement:
--   The Height Vanishing construction uses the eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L235-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L235-L272

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
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
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)
variable {P : Type} [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.HeightVanishing.eval {d : ℕ} {g : Module.End ℂ (TV n M P)} (hg : Deg E d g) (J : P → Fin n) :
    ∀ I : P → Fin n, ∃ A ∈ W E d (H J I), ∀ v, g (Pi.single I v) J = A v := by sorry
