-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_locDens_cons_congr_1469dadc76d5
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_locDens_cons_congr_1469dadc76d5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:49.650091+00:00
-- url     : https://prove2.me/theorems/595dfa52-1661-4c76-aef1-d6d331c73766
-- title:
--   P2 M Ground Theory Heights  Heights Four B Compact Support Stokes loc Dens cons congr 1469dadc76d5: P2 M Ground Theory Heights  Heights Four B Compact Support Stokes loc Dens cons congr 1469dadc76d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Compact Support Stokes loc Dens cons congr 1469dadc76d5 construction uses the P2 M Ground Theory Heights  Heights Four B Compact Support Stokes loc Dens cons congr 1469dadc76d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L33-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_locDens_cons_congr_1469dadc76d5 (A : FinHolAtlas (e + 1) X) {P Q : LocPot X} (Φ : Fin e → LocPot X)
    (h : P.φ = Q.φ) (k : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons P Φ) k y = locDens A (Fin.cons Q Φ) k y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CompactSupportStokes».«locDens_cons_congr» := P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_locDens_cons_congr_1469dadc76d5
