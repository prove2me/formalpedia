-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_plusMetric_joinPt_ee8b088ced98
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_plusMetric_joinPt_ee8b088ced98
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:12.40846+00:00
-- url     : https://prove2.me/theorems/4abdb07f-9188-47a0-9514-8f336284b96b
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections plus Metric join Pt ee8b088ced98: P2 M Ground Theory Heights  Heights Small Sections plus Metric join Pt ee8b088ced98
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections plus Metric join Pt ee8b088ced98 construction uses the P2 M Ground Theory Heights  Heights Small Sections plus Metric join Pt ee8b088ced98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L246-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L246-L281

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SmallSections_plusMetric_joinPt_ee8b088ced98 {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    (N : HermLine n) {r : ℕ} {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ}
    (hG : P.IsHomogGenerators G δ)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) :
    D.plusMetric N d g G δ (D.joinPt z (fun j ↦ evalCone z (g c j))) =
      ‖evalCone z (chartMonomial c d)‖ * N.metric z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«plusMetric_joinPt» := P2M_GroundTheory_Heights__Heights_SmallSections_plusMetric_joinPt_ee8b088ced98
