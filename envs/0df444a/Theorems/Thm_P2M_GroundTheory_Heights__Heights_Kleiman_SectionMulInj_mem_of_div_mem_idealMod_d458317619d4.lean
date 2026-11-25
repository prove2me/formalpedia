-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_of_div_mem_idealMod_d458317619d4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_of_div_mem_idealMod_d458317619d4
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:19:18.396326+00:00
-- url     : https://prove2.me/theorems/62846e46-65b4-5379-99b2-45d5662ede07
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj mem of div mem ideal Mod d458317619d4: P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj mem of div mem ideal Mod d458317619d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj mem of div mem ideal Mod d458317619d4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj mem of div mem ideal Mod d458317619d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionMulInj.lean#L51-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionMulInj.lean#L51-L66

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_of_div_mem_idealMod_d458317619d4 {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {F m : Poly S N} {e : ℕ} (hm : m ∈ monos I.1)
    (hF : F.IsHomogeneous e) (hme : m.IsHomogeneous e) (h : aeval x F / aeval x m ∈ idealMod (x := x) pp I) :
    F ∈ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionMulInj».«mem_of_div_mem_idealMod» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_of_div_mem_idealMod_d458317619d4
