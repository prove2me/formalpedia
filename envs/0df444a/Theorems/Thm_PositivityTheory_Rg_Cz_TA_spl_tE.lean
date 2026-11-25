-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_spl_tE
-- name    : PositivityTheory.Rg.Cz.TA.spl_tE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:06.223087+00:00
-- url     : https://prove2.me/theorems/c62a5423-751c-4535-87c9-94023be5ad7d
-- title:
--   TA: spl t E
-- statement:
--   The TA construction uses the spl t E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllB.lean#L72-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllB.lean#L72-L90

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
omit [Fintype P]

theorem PositivityTheory.Rg.Cz.TA.spl_tE (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    spl q (tE S F a b f) =
      tE (S.subtype q) (fun a b => tE (S.subtype fun p => ¬ q p) F a b) a b (spl q f) := by sorry
