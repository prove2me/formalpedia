-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_word_cons
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.word_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:05.539824+00:00
-- url     : https://prove2.me/theorems/1b1b08d6-35c2-4665-9354-0804137c5897
-- title:
--   Height Vanishing: word cons
-- statement:
--   The Height Vanishing construction uses the word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L27-L28

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

theorem PositivityTheory.Rg.Cz.HeightVanishing.word_cons (x : Fin n × Fin n) (w : List (Fin n × Fin n)) : word E (x :: w) = E x.1 x.2 * word E w := by sorry
