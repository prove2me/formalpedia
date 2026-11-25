-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_evA
-- name    : PositivityTheory.Rg.Cz.QuantumDeterminantProducts.evA
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:49:37.201799+00:00
-- url     : https://prove2.me/theorems/73dc661c-098e-483b-9d97-8cb333b851d1
-- title:
--   Quantum Determinant Products: ev A
-- statement:
--   The Quantum Determinant Products construction uses the ev A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L144-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L144-L148

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
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
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.QuantumDeterminantProducts.evA (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (I : Fin n → Fin n) :
    (l.map (T E u)).prod h I = ev E u l I h := by sorry
