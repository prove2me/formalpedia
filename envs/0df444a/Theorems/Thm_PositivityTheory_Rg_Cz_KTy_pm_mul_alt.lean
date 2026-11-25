-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_pm_mul_alt
-- name    : PositivityTheory.Rg.Cz.KTy.pm_mul_alt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:05.263835+00:00
-- url     : https://prove2.me/theorems/6f82a2c6-9004-4cbc-a413-ae49b3afd868
-- title:
--   KTy: pm mul alt
-- statement:
--   The KTy construction uses the pm mul alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L186-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L186-L199

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
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
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem PositivityTheory.Rg.Cz.KTy.pm_mul_alt {P : Type} [Fintype P] [DecidableEq P] {M : Type} [AddCommGroup M] [Module ℂ M]
    (G : Finset (Equiv.Perm P)) (σ₀ : Equiv.Perm P) (h : ∀ σ, σ₀ * σ ∈ G ↔ σ ∈ G) :
    (pm σ₀ * alt G : Module.End ℂ (TV n M P)) = ((Equiv.Perm.sign σ₀ : ℤ) : ℂ) • alt G := by sorry
