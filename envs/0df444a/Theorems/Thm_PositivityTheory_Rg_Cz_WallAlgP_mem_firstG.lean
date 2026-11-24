-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_mem_firstG
-- name    : PositivityTheory.Rg.Cz.WallAlgP.mem_firstG
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:40.34759+00:00
-- url     : https://prove2.me/theorems/7afbf23b-4a5a-4f8e-941a-10d532aa8f58
-- title:
--   Wall Alg P: mem first G
-- statement:
--   The Wall Alg P construction uses the mem first G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L25-L27

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

theorem PositivityTheory.Rg.Cz.WallAlgP.mem_firstG {m k : ℕ} (σ : Equiv.Perm (Fin m)) :
    σ ∈ firstG m k ↔ ∀ j : Fin m, k ≤ (j : ℕ) → σ j = j := by sorry
