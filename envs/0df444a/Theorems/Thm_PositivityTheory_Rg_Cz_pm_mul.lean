-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul
-- name    : PositivityTheory.Rg.Cz.pm_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:07.104199+00:00
-- url     : https://prove2.me/theorems/41fa8542-2128-40a9-b990-0175d7d64b18
-- title:
--   Cz: pm mul
-- statement:
--   The Cz construction uses the pm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L40-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L40-L40

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
omit [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.pm_mul (σ τ : Equiv.Perm P) : (pm (σ * τ) : Module.End ℂ (TV n M P)) = pm σ * pm τ := by sorry
