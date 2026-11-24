-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_prod_split
-- name    : PositivityTheory.Rg.Cz.TGK.prod_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:53.943637+00:00
-- url     : https://prove2.me/theorems/c72b947a-937d-4b40-b425-b366299fdb7f
-- title:
--   TGK: prod split
-- statement:
--   The TGK construction uses the prod split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L84-L85

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TGK.prod_split (p : P) (g : P → ℂ) : ∏ q, g q = g p * ∏ q ∈ Finset.univ.erase p, g q := by sorry
