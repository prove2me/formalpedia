-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_comm_mem
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.comm_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:17.138314+00:00
-- url     : https://prove2.me/theorems/34dbadb2-a5d8-48cf-9b42-302f4a37a9c0
-- title:
--   Height Vanishing: comm mem
-- statement:
--   The Height Vanishing construction uses the comm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L71-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L71-L110

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

theorem PositivityTheory.Rg.Cz.HeightVanishing.comm_mem (hE : GlRel E) (a b : Fin n) {k : ℕ} {h : ℤ} {A : Module.End ℂ M} (hA : A ∈ W E k h) :
    E a b * A - A * E a b ∈ W E k (h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) := by sorry
