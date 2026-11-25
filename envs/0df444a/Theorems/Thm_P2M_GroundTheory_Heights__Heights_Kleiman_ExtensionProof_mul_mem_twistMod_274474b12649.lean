-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mul_mem_twistMod_274474b12649
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mul_mem_twistMod_274474b12649
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:34.663861+00:00
-- url     : https://prove2.me/theorems/8bc8906b-806c-476c-bffc-ec72d017a108
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof mul mem twist Mod 274474b12649: P2 M Ground Theory Heights  Heights Kleiman Extension Proof mul mem twist Mod 274474b12649
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof mul mem twist Mod 274474b12649 construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof mul mem twist Mod 274474b12649 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L34-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mul_mem_twistMod_274474b12649 {J : Chart x} {f s : Poly S N} {e e' : ℕ} {d c : ℤ} (hs : s ∈ monos J.1)
    (hf : f.IsHomogeneous e') (hse : s.IsHomogeneous e) (hd : (e' : ℤ) = e + d) {q : Ω}
    (hq : q ∈ twistMod S x c J) : aeval x f / aeval x s * q ∈ twistMod S x (c + d) J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«mul_mem_twistMod» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mul_mem_twistMod_274474b12649
