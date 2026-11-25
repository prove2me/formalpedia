-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_div_eq_of_isFrac_5a8880453f6c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_div_eq_of_isFrac_5a8880453f6c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:21.413028+00:00
-- url     : https://prove2.me/theorems/fd08d8db-6230-40df-ba1a-c924eb212896
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist div eq of is Frac 5a8880453f6c: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist div eq of is Frac 5a8880453f6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist div eq of is Frac 5a8880453f6c construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist div eq of is Frac 5a8880453f6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L73-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L73-L93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_div_eq_of_isFrac_5a8880453f6c {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) {c : ℤ} {I J : Finset (Fin (N + 1))} {z : Ω}
    {t t' : Poly S N × Poly S N × ℕ × ℕ} (h : IsFrac x c I z t) (h' : IsFrac x c J z t')
    (hx : aeval x t.2.1 ≠ 0) (hx' : aeval x t'.2.1 ≠ 0) (hy : aeval y t.2.1 ≠ 0)
    (hy' : aeval y t'.2.1 ≠ 0) :
    aeval y t.1 / aeval y t.2.1 = aeval y t'.1 / aeval y t'.2.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«div_eq_of_isFrac» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_div_eq_of_isFrac_5a8880453f6c
