-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_eAt_apply
-- name    : PositivityTheory.Rg.Cz.eAt_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:17.450521+00:00
-- url     : https://prove2.me/theorems/883757ce-d3f2-40a8-af25-2fda269296e5
-- title:
--   Cz: e At apply
-- statement:
--   The Cz construction uses the e At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L15-L18

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P]

theorem PositivityTheory.Rg.Cz.eAt_apply (p : P) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    eAt p a b f I = if I p = a then f (Function.update I p b) else 0 := by sorry
