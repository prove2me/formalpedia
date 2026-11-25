-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_pm_single
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.pm_single
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:03.409228+00:00
-- url     : https://prove2.me/theorems/5579a952-c38c-4288-9721-70ff4ac3b76a
-- title:
--   Height Vanishing: pm single
-- statement:
--   The Height Vanishing construction uses the pm single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L227-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L227-L231

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

theorem PositivityTheory.Rg.Cz.HeightVanishing.pm_single (σ : Equiv.Perm P) (I : P → Fin n) (v : M) :
    pm σ (Pi.single I v : TV n M P) = Pi.single (I ∘ σ.symm) v := by sorry
