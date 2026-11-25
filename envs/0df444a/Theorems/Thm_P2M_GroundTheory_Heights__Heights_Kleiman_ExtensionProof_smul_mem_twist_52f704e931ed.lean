-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_twist_52f704e931ed
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_twist_52f704e931ed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:22.029806+00:00
-- url     : https://prove2.me/theorems/dff04a54-d778-4d45-b3dd-98ef0c4ca5b3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof smul mem twist 52f704e931ed: P2 M Ground Theory Heights  Heights Kleiman Extension Proof smul mem twist 52f704e931ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof smul mem twist 52f704e931ed construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof smul mem twist 52f704e931ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L51-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L51-L66

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
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_twist_52f704e931ed (F : SubSystem S x E) {J : Chart x} {f s : Poly S N} {e e' : ℕ} {d c : ℤ}
    (hs : s ∈ monos J.1) (hf : f.IsHomogeneous e') (hse : s.IsHomogeneous e) (hd : (e' : ℤ) = e + d)
    {m : E} (hm : m ∈ (F.twist (twistSys S x c)).sub J) :
    (aeval x f / aeval x s) • m ∈ (F.twist (twistSys S x (c + d))).sub J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«smul_mem_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_twist_52f704e931ed
