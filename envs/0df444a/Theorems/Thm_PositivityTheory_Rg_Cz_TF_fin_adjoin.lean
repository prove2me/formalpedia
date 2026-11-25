-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TF_fin_adjoin
-- name    : PositivityTheory.Rg.Cz.TF.fin_adjoin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:40.197847+00:00
-- url     : https://prove2.me/theorems/c8cea24f-013e-48de-b92e-72b7358560e7
-- title:
--   TF: fin adjoin
-- statement:
--   The TF construction uses the fin adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinF.lean#L16-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinF.lean#L16-L53

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF

theorem PositivityTheory.Rg.Cz.TF.fin_adjoin {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [Finite ι] (x : ι → A)
    (hc : ∀ i j, Commute (x i) (x j)) (hL : ∀ i, ∃ L : List ℂ, (L.map fun c => x i - algebraMap ℂ A c).prod = 0) :
    FiniteDimensional ℂ (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range x))) := by sorry
