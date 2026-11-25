-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_mul_mem_span_1b6ac5c8ed25
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_mul_mem_span_1b6ac5c8ed25
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:15.096255+00:00
-- url     : https://prove2.me/theorems/d37faf74-5ac4-4008-8ddd-b048039b526a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin chart mul mem span 1b6ac5c8ed25: P2 M Ground Theory Heights  Heights Kleiman Twist Fin chart mul mem span 1b6ac5c8ed25
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin chart mul mem span 1b6ac5c8ed25 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin chart mul mem span 1b6ac5c8ed25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L96-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L96-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
variable (M0 : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_mul_mem_span_1b6ac5c8ed25 (I : Chart x) (b : ℕ) (c : chartRing S x I) {ω : Ω}
    (hω : ω ∈ Submodule.span S (genSet x η S M0 I b)) :
    (c : Ω) * ω ∈ Submodule.span S (genSet x η S M0 I b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«chart_mul_mem_span» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_mul_mem_span_1b6ac5c8ed25
