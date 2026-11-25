-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_algebraMap_2078138e67d2
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_algebraMap_2078138e67d2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:45.2147+00:00
-- url     : https://prove2.me/theorems/8b03450b-c96b-4c43-996c-b9303bbab061
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Domain to Poly algebra Map 2078138e67d2: P2 M Ground Theory Heights  Heights Vertical Chart Domain to Poly algebra Map 2078138e67d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Domain to Poly algebra Map 2078138e67d2 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Domain to Poly algebra Map 2078138e67d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L168-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L168-L171

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_algebraMap_2078138e67d2 (d : D) : toPoly Q j e (algebraMap D (Chart Q j e) d) = κ Q j e d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartDomain».«toPoly_algebraMap» := P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_algebraMap_2078138e67d2
