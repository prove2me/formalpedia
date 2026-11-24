-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_omc_glue_j
-- name    : PositivityTheory.Rg.Cz.CtrX.omc_glue_j
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:02.772144+00:00
-- url     : https://prove2.me/theorems/194fef19-0aed-40a7-b702-630a782fc08b
-- title:
--   Ctr X: omc glue j
-- statement:
--   The Ctr X construction uses the omc glue j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractE.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractE.lean#L36-L37

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
omit [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.CtrX.omc_glue_j {m : ℕ} (j : Fin m) (b : Fin n) (R : {p // p ≠ j} → Fin n) : omcGlue j b R j = b := by sorry
