-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_spl_apply
-- name    : PositivityTheory.Rg.Cz.TA.spl_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:38.561099+00:00
-- url     : https://prove2.me/theorems/ec3b4be2-5090-4d0c-8e3f-a359232746f2
-- title:
--   TA: spl apply
-- statement:
--   The TA construction uses the spl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllB.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllB.lean#L68-L69

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]
omit [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TA.spl_apply (F : TV n M P) (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) :
    spl q F J I = F (merge q J I) := by sorry
