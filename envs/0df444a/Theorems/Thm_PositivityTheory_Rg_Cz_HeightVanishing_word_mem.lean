-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_word_mem
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.word_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:27.789423+00:00
-- url     : https://prove2.me/theorems/c6f23349-a72f-440c-8c9d-95b0d15bd8c4
-- title:
--   Height Vanishing: word mem
-- statement:
--   The Height Vanishing construction uses the word mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L30-L31

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

theorem PositivityTheory.Rg.Cz.HeightVanishing.word_mem {k : ℕ} {h : ℤ} (w : List (Fin n × Fin n)) (hk : w.length ≤ k) (hh : ht w = h) :
    word E w ∈ W E k h := by sorry
