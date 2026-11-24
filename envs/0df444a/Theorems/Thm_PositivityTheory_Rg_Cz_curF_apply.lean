-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_curF_apply
-- name    : PositivityTheory.Rg.Cz.curF_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:46.53136+00:00
-- url     : https://prove2.me/theorems/78d815d7-1868-4d7d-b965-29a94f444841
-- title:
--   Cz: cur F apply
-- statement:
--   The Cz construction uses the cur F apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L78-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L78-L79

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

theorem PositivityTheory.Rg.Cz.curF_apply {m k : ℕ} (f : TV n M (Fin (m + k))) (J : Fin k → Fin n) (I : Fin m → Fin n) :
    curF n M m k f J I = f (Fin.append I J) := by sorry
