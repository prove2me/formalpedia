-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_num_den_not_mem_fc51e55aaf89
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_num_den_not_mem_fc51e55aaf89
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:10.289737+00:00
-- url     : https://prove2.me/theorems/4f4ceac0-6f68-45e3-bf5e-11a906732bc2
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms num den not mem fc51e55aaf89: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms num den not mem fc51e55a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms num den not mem fc51e55aaf89 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms num den not mem fc51e55aaf89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L104-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L104-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_num_den_not_mem_c51964657b3c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_num_den_not_mem_fc51e55aaf89 {P : Ideal (MRing ι)} (hP : P.IsPrime) (g : (Σ k, ι₂ k) → MRing ι) {j : ∀ k, ι₂ k}
    (hj : ∀ k, g ⟨k, j k⟩ ∉ P) (a : K₂ → ℤ) :
    num g j a ∉ graphIdeal P g ∧ den g j a ∉ graphIdeal P g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«num_den_not_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_num_den_not_mem_fc51e55aaf89
