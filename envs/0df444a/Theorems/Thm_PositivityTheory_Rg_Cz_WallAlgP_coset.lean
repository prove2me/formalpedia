-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_coset
-- name    : PositivityTheory.Rg.Cz.WallAlgP.coset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:45.059198+00:00
-- url     : https://prove2.me/theorems/5b795df5-f4a2-419a-a272-69398ab5f148
-- title:
--   Wall Alg P: coset
-- statement:
--   The Wall Alg P construction uses the coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L115-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L115-L166

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

theorem PositivityTheory.Rg.Cz.WallAlgP.coset {m k : ℕ} (hk : k < m) {V : Type} [AddCommMonoid V] (f : Equiv.Perm (Fin m) → V) :
    ∑ τ ∈ firstG m (k + 1), f τ = ∑ σ ∈ firstG m k, f σ +
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), ∑ σ ∈ firstG m k, f (Equiv.swap j ⟨k, hk⟩ * σ) := by sorry
