-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_vecCons_comp_613af14c7f72
-- name    : P2M_GroundTheory_Heights__Heights_vecCons_comp_613af14c7f72
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:08.675735+00:00
-- url     : https://prove2.me/theorems/c3cca60a-0c30-4ef2-b70d-d0314d97dc88
-- title:
--   P2 M Ground Theory Heights  Heights vec Cons comp 613af14c7f72: P2 M Ground Theory Heights  Heights vec Cons comp 613af14c7f72
-- statement:
--   The P2 M Ground Theory Heights  Heights vec Cons comp 613af14c7f72 construction uses the P2 M Ground Theory Heights  Heights vec Cons comp 613af14c7f72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L48-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCutHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_vecCons_comp_613af14c7f72 {D : ℕ} (f : (Fin n → ℂ) → ℝ) (φ : Fin D → (Fin n → ℂ) → ℝ)
    (s : (Fin (D + 1) → ℂ) → Fin n → ℂ) :
    (fun k => (vecCons f φ : Fin (D + 1) → (Fin n → ℂ) → ℝ) k ∘ s) = Fin.cons (f ∘ s) (fun k => φ k ∘ s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«vecCons_comp» := P2M_GroundTheory_Heights__Heights_vecCons_comp_613af14c7f72
