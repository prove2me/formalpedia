-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_count_eqb
-- name    : PositivityTheory.Rg.Cz.count_eqb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:13.075278+00:00
-- url     : https://prove2.me/theorems/fdc78d3b-d2b1-41eb-84c7-3ccebb7eecfc
-- title:
--   Cz: count eqb
-- statement:
--   The Cz construction uses the count eqb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/CountSame.lean#L46-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/CountSame.lean#L46-L69

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountSame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}

theorem PositivityTheory.Rg.Cz.count_eqb (hT : IsTab col b) (p : Q) (hp : p ∈ S) :
    ((S.filter fun q => b q = b p).card : ℝ) =
      1 + ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then (1 : ℝ) else 0) := by sorry
