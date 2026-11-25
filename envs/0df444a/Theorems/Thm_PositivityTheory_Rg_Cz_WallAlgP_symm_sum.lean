-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_symm_sum
-- name    : PositivityTheory.Rg.Cz.WallAlgP.symm_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:48.040339+00:00
-- url     : https://prove2.me/theorems/81c24bd0-ccae-4d97-882d-a6a33a4af935
-- title:
--   Wall Alg P: symm sum
-- statement:
--   The Wall Alg P construction uses the symm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L216-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L216-L242

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.WallAlgP.symm_sum {m k : ℕ} {V : Type} [AddCommMonoid V] (g : Fin m → Fin m → V) (hg : ∀ i j, g i j = g j i) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k),
      ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ p ≠ j), g j p =
    2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), ∑ i ∈ Finset.univ.filter (· < j), g i j := by sorry
