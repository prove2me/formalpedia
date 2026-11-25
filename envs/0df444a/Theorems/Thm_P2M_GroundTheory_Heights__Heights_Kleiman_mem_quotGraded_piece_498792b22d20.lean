-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_quotGraded_piece_498792b22d20
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_quotGraded_piece_498792b22d20
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:54.372495+00:00
-- url     : https://prove2.me/theorems/1dd5086e-9cf1-40ab-a022-a65c542c58da
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem quot Graded piece 498792b22d20: P2 M Ground Theory Heights  Heights Kleiman mem quot Graded piece 498792b22d20
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem quot Graded piece 498792b22d20 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem quot Graded piece 498792b22d20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/QuotGraded.lean#L157-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/QuotGraded.lean#L157-L165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
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
open MvPolynomial DirectSum
noncomputable section
universe u
variable {S : Type u} [CommRing S] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_quotGraded_piece_498792b22d20 {p : Ideal (Poly S N)} {hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p}
    {c : ℤ} {m : Poly S N ⧸ p} :
    m ∈ (quotGraded p hp).piece c ↔ ∃ f : Poly S N,
      IsWeightedHomogeneous (fun _ => (1 : ℤ)) f c ∧ Ideal.Quotient.mk p f = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_quotGraded_piece» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_quotGraded_piece_498792b22d20
