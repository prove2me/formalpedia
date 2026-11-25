-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_evQ
-- name    : PositivityTheory.Rg.Cz.QuantumDeterminantProducts.evQ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:30.848855+00:00
-- url     : https://prove2.me/theorems/6606c1f8-7c51-465c-a37b-2b1aa6f2ee17
-- title:
--   Quantum Determinant Products: ev Q
-- statement:
--   The Quantum Determinant Products construction uses the ev Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L199-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L199-L220

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

theorem PositivityTheory.Rg.Cz.QuantumDeterminantProducts.evQ (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (g : TV n M (Fin n)) (hg : IsAnti g) :
    ev E u (List.finRange n) id g = qdet E u (g id) := by sorry
