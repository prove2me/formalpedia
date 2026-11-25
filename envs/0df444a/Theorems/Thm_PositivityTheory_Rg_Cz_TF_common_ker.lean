-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TF_common_ker
-- name    : PositivityTheory.Rg.Cz.TF.common_ker
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:27.017854+00:00
-- url     : https://prove2.me/theorems/2beafb7e-5e10-4b44-b6be-dca732f22335
-- title:
--   TF: common ker
-- statement:
--   The TF construction uses the common ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinCK.lean#L44-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinCK.lean#L44-L79

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF

theorem PositivityTheory.Rg.Cz.TF.common_ker {U : Type*} [AddCommGroup U] [Module ℂ U] (T : ℕ → Module.End ℂ U)
    (hT : ∀ i j, Commute (T i) (T j)) (e : U →ₗ[ℂ] ℂ) (s : Finset ℕ) :
    ∀ Z : Submodule ℂ U, FiniteDimensional ℂ Z → (∀ i ∈ s, ∀ z ∈ Z, T i z ∈ Z) →
      (∀ i ∈ s, ∀ z ∈ Z, e (T i z) = 0) → (∃ z ∈ Z, e z ≠ 0) → ∃ z ∈ Z, z ≠ 0 ∧ ∀ i ∈ s, T i z = 0 := by sorry
