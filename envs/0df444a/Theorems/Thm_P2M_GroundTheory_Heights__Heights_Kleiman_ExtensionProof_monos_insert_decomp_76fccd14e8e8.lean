-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_monos_insert_decomp_76fccd14e8e8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_monos_insert_decomp_76fccd14e8e8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:18.560535+00:00
-- url     : https://prove2.me/theorems/35ce7375-6310-4491-9512-aa97d34e091b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof monos insert decomp 76fccd14e8e8: P2 M Ground Theory Heights  Heights Kleiman Extension Proof monos insert decomp 76fccd14e8e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof monos insert decomp 76fccd14e8e8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof monos insert decomp 76fccd14e8e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L19-L32

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_monos_insert_decomp_76fccd14e8e8 {i : Fin (N + 1)} {J : Finset (Fin (N + 1))} {s : Poly S N}
    (hs : s ∈ monos (insert i J)) : ∃ (p : ℕ) (t : Poly S N), t ∈ monos J ∧ s = X i ^ p * t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«monos_insert_decomp» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_monos_insert_decomp_76fccd14e8e8
