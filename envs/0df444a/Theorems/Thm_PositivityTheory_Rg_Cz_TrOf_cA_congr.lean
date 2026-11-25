-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TrOf_cA_congr
-- name    : PositivityTheory.Rg.Cz.TrOf.cA_congr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:36.766539+00:00
-- url     : https://prove2.me/theorems/b4f05a75-759b-4d0e-9e9c-cd15f8ff1b7d
-- title:
--   Tr Of: c A congr
-- statement:
--   The Tr Of construction uses the c A congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L54-L59

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
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
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

theorem PositivityTheory.Rg.Cz.TrOf.cA_congr {C C' : Type} [DecidableEq C] [DecidableEq C'] (c1 : Q → C) (c2 : Q → C')
    (h : ∀ p q, c1 p = c1 q ↔ c2 p = c2 q) (b : Q → Fin n) : (cA c1 b : TV n M Q →ₗ[ℂ] M) = cA c2 b := by sorry
