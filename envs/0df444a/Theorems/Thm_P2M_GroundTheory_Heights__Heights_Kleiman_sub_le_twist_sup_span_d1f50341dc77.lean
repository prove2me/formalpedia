-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sub_le_twist_sup_span_d1f50341dc77
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_sub_le_twist_sup_span_d1f50341dc77
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:02:42.417958+00:00
-- url     : https://prove2.me/theorems/d1ecba53-463c-4661-80b1-fcf47d0f884f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman sub le twist sup span d1f50341dc77: P2 M Ground Theory Heights  Heights Kleiman sub le twist sup span d1f50341dc77
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman sub le twist sup span d1f50341dc77 construction uses the P2 M Ground Theory Heights  Heights Kleiman sub le twist sup span d1f50341dc77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutNonempty.lean#L53-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutNonempty.lean#L53-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutNonempty
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_sub_le_twist_sup_span_d1f50341dc77 {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) (L : LineBundle k x) (s : Ω)
    (hmin : ∀ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, ∀ i, (X i : Poly k N) ∈ qq)
    (j : Fin (N + 1)) (hj : x j ≠ 0) :
    L.sub (singleChart hj) ≤ (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
      Submodule.span (chartRing k x (singleChart hj)) {s} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«sub_le_twist_sup_span» := P2M_GroundTheory_Heights__Heights_Kleiman_sub_le_twist_sup_span_d1f50341dc77
