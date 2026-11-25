-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_mem_mcPts_of_conePts_d1e60471d38c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_mem_mcPts_of_conePts_d1e60471d38c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:46.245912+00:00
-- url     : https://prove2.me/theorems/1530389f-fa4e-51fe-8e4b-05d010ea52c3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite mem mc Pts of cone Pts d1e60471d38c: P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite mem mc
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite mem mc Pts of cone Pts d1e60471d38c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite mem mc Pts of cone Pts d1e60471d38c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComponentResFibreFinite.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComponentResFibreFinite.lean#L28-L31

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
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_mem_mcPts_of_conePts_d1e60471d38c {P : Ideal (MRing ι)}
    (hW : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ ReciprocityTheory.AnForm.R.conePts W) : z ∈ mcPts P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ComponentResFibreFinite».«mem_mcPts_of_conePts» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_mem_mcPts_of_conePts_d1e60471d38c
