-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_smul_segre_mem_fibre_954212387671
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_smul_segre_mem_fibre_954212387671
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:18:05.974797+00:00
-- url     : https://prove2.me/theorems/826c73ba-e094-4cf8-89c4-f9a1ef4ce8ae
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite smul segre mem fibre 954212387671: P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite smul segr
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite smul segre mem fibre 954212387671 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite smul segre mem fibre 954212387671 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComponentResFibreFinite.lean#L33-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComponentResFibreFinite.lean#L33-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComponentResFibreFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_smul_segre_mem_fibre_954212387671 {P : Ideal (MRing ι)} (hK : Nonempty K) (hPh : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (h0 : Ψ (segre z) 0 ≠ 0) :
    (Ψ (segre z) 0)⁻¹ • segre z ∈
      fibre P Ψ (fun i : Fin e => Ψ (segre z) i.succ / Ψ (segre z) 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ComponentResFibreFinite».«smul_segre_mem_fibre» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_smul_segre_mem_fibre_954212387671
