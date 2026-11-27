-- Prove2me | Theorems.Thm_PvsNP_McspBicoloredOverlap_exists_overlapping_equality_subfamily
-- name    : PvsNP.McspBicoloredOverlap.exists_overlapping_equality_subfamily
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T04:48:35.033509+00:00
-- url     : https://prove2.me/theorems/910c171a-0c5f-5a04-839a-a8954ce6cd09
-- title:
--   Finite decoder yields an equality subfamily at every common-middle cut
-- statement:
--   Let M labels specify two blocks each, with injective left and right block maps and a common left-block length. Form a word by appending a common middle block and the independently chosen right block to a chosen left block. Suppose each word formed using the same label on both sides is accepted. Suppose every accepted mixed word is decoded by some element of a finite code space of size B. There is a set S of labels such that M² + M|S| ≤ 2B|S|. For every cut in the common middle block, the prefix of an accepted diagonal word for a label in S and the suffix of an accepted diagonal word for a label in S form an accepted word exactly when the two labels coincide.
-- source:
--   Finite combinatorial lemma using Turán’s theorem. Motivated by sparse truth table splicing for MCSP with pre-existing finite circuit decoders. The conclusion is conditional on accepted diagonals and coverage by the decoder.

import Mathlib

theorem PvsNP.McspBicoloredOverlap.exists_overlapping_equality_subfamily
    {α β σ : Type*} [Fintype α] [Fintype σ] (left right : α → List β)
    (gap : List β) (len : ℕ) (hleft : ∀ a, (left a).length = len)
    (hleft_inj : Function.Injective left) (hright_inj : Function.Injective right)
    (accept : List β → Prop) [DecidablePred accept] (decode : σ → List β)
    (hdiag : ∀ a, accept (left a ++ gap ++ right a))
    (hcover : ∀ a b, accept (left a ++ gap ++ right b) →
      ∃ code, decode code = left a ++ gap ++ right b) :
    ∃ s : Finset α,
      (Fintype.card α)^2 + Fintype.card α * s.card ≤ (2 * Fintype.card σ) * s.card ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ cut, len ≤ cut → cut ≤ len + gap.length →
        (accept ((left a ++ gap ++ right a).take cut ++
          (left b ++ gap ++ right b).drop cut) ↔ a = b) := by sorry
