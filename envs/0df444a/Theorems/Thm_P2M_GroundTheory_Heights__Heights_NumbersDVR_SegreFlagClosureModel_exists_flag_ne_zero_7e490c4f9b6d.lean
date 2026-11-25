-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureModel_exists_flag_ne_zero_7e490c4f9b6d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureModel_exists_flag_ne_zero_7e490c4f9b6d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:17:13.824158+00:00
-- url     : https://prove2.me/theorems/e95e61a4-0d49-5651-b838-200d9cf574da
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Model exists flag ne zero 7e490c4f9b6d: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Model exists flag ne zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Model exists flag ne zero 7e490c4f9b6d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Model exists flag ne zero 7e490c4f9b6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosureModel.lean#L18-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosureModel.lean#L18-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureModel

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureModel_exists_flag_ne_zero_7e490c4f9b6d {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (w e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∃ l, ∑ j, flagCoord w e t k j * algebraMap Ω Φ (ψ l (w j)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagClosureModel».«exists_flag_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureModel_exists_flag_ne_zero_7e490c4f9b6d
