-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_anti_ext
-- name    : PositivityTheory.Rg.Cz.QuantumDeterminantProducts.anti_ext
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:08.594479+00:00
-- url     : https://prove2.me/theorems/cbaa0b80-25d2-4d9a-873a-46a004ed1e2f
-- title:
--   Quantum Determinant Products: anti ext
-- statement:
--   The Quantum Determinant Products construction uses the anti ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L46-L56

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

theorem PositivityTheory.Rg.Cz.QuantumDeterminantProducts.anti_ext {g : TV n M (Fin n)} (hg : IsAnti g) (h0 : g id = 0) : g = 0 := by sorry
