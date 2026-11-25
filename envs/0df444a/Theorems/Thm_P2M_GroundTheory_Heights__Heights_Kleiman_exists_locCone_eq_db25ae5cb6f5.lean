-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_locCone_eq_db25ae5cb6f5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_locCone_eq_db25ae5cb6f5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:27.069815+00:00
-- url     : https://prove2.me/theorems/b1e30603-feab-427b-b21d-970c2b834b5f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists loc Cone eq db25ae5cb6f5: P2 M Ground Theory Heights  Heights Kleiman exists loc Cone eq db25ae5cb6f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists loc Cone eq db25ae5cb6f5 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists loc Cone eq db25ae5cb6f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L142-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L142-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_locCone_eq_db25ae5cb6f5 (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {y : Ω}
    (hy : y ∈ M.tilde c ⟨I.1, I.2.1, hI⟩) :
    ∃ z ∈ degLoc M.coneGraded c I, locCone M I.1 hI z = coneSingle S x c y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_locCone_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_locCone_eq_db25ae5cb6f5
