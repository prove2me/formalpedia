-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_or_mem_3afecbde79cc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_or_mem_3afecbde79cc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:11:25.821827+00:00
-- url     : https://prove2.me/theorems/5d468fd5-b5c3-4df5-97f1-468d817c9f7e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj mem or mem 3afecbde79cc: P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj mem or mem 3afecbde79cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj mem or mem 3afecbde79cc construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj mem or mem 3afecbde79cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionMulInj.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionMulInj.lean#L68-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionMulInj
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
open GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_or_mem_3afecbde79cc {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) (a b : chartRing S x I)
    (h : (a : Ω) * b ∈ idealMod (x := x) pp I) :
    (a : Ω) ∈ idealMod (x := x) pp I ∨ (b : Ω) ∈ idealMod (x := x) pp I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionMulInj».«mem_or_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_or_mem_3afecbde79cc
