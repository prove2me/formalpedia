-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_alt_perm
-- name    : PositivityTheory.Rg.Cz.YoungTableau.alt_perm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:19.092871+00:00
-- url     : https://prove2.me/theorems/c409bf0f-3489-4748-a808-46c2a22b4f55
-- title:
--   Young Tableau: alt perm
-- statement:
--   The Young Tableau construction uses the alt perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L21-L44

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
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
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]

theorem PositivityTheory.Rg.Cz.YoungTableau.alt_perm (col : X → C) (ξ : TV n M X) (J : X → Fin n) (π : Equiv.Perm X) (hπ : π ∈ colG col) :
    alt (colG col) ξ (J ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • alt (colG col) ξ J := by sorry
