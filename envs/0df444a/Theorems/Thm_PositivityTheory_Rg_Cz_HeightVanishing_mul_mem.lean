-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_mul_mem
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.mul_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:13.829433+00:00
-- url     : https://prove2.me/theorems/c10b47fc-05ba-4f7e-a89e-d7e4f53bb177
-- title:
--   Height Vanishing: mul mem
-- statement:
--   The Height Vanishing construction uses the mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L52-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L52-L69

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

theorem PositivityTheory.Rg.Cz.HeightVanishing.mul_mem {k k' : ℕ} {h h' : ℤ} {A B : Module.End ℂ M} (hA : A ∈ W E k h) (hB : B ∈ W E k' h') :
    A * B ∈ W E (k + k') (h + h') := by sorry
