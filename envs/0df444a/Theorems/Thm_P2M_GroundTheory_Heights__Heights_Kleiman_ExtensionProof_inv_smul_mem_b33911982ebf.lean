-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_inv_smul_mem_b33911982ebf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_inv_smul_mem_b33911982ebf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:37.935803+00:00
-- url     : https://prove2.me/theorems/f37404da-c937-4a55-9303-8376946c2662
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof inv smul mem b33911982ebf: P2 M Ground Theory Heights  Heights Kleiman Extension Proof inv smul mem b33911982ebf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof inv smul mem b33911982ebf construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof inv smul mem b33911982ebf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L94-L100

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_inv_smul_mem_b33911982ebf (F : SubSystem S x E) {I : Chart x} {c : ℤ} {m : E}
    (hm : m ∈ (F.twist (twistSys S x c)).sub I) {s : Poly S N} {e : ℕ} (hs : s ∈ monos I.1)
    (hse : s.IsHomogeneous e) (hec : (e : ℤ) = c) : (aeval x s)⁻¹ • m ∈ F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«inv_smul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_inv_smul_mem_b33911982ebf
