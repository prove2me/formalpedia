-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TrOf_rl_apply
-- name    : PositivityTheory.Rg.Cz.TrOf.rl_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:21.101614+00:00
-- url     : https://prove2.me/theorems/4ec9246e-4c6f-4ed6-a0f3-f0dbe0fc5287
-- title:
--   Tr Of: rl apply
-- statement:
--   The Tr Of construction uses the rl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L24-L24

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
omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

theorem PositivityTheory.Rg.Cz.TrOf.rl_apply (e : P ≃ Q) (f : TV n M P) (J : Q → Fin n) : rl e f J = f (J ∘ e) := by sorry
