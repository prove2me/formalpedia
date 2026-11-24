-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_sg_swap
-- name    : PositivityTheory.Rg.Cz.QuantumDeterminantProducts.sg_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:09.341524+00:00
-- url     : https://prove2.me/theorems/5794476e-941d-4a4a-ab0d-1bdd7296c876
-- title:
--   Quantum Determinant Products: sg swap
-- statement:
--   The Quantum Determinant Products construction uses the sg swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L15-L16

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

theorem PositivityTheory.Rg.Cz.QuantumDeterminantProducts.sg_swap {i j : Fin n} (h : i ≠ j) : sg (Equiv.swap i j) = -1 := by sorry
