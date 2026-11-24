-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
-- name    : PositivityTheory.Rg.Cz.pm_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:52.301841+00:00
-- url     : https://prove2.me/theorems/ce9073cb-4bd8-402a-b3c5-4c5c1691cc73
-- title:
--   Cz: pm apply
-- statement:
--   The Cz construction uses the pm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L21-L21

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

theorem PositivityTheory.Rg.Cz.pm_apply (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) : pm σ f I = f (I ∘ σ) := by sorry

attribute [defeq] PositivityTheory.Rg.Cz.pm_apply
