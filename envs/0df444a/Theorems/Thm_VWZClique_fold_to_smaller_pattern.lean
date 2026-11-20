-- Prove2me | Theorems.Thm_VWZClique_fold_to_smaller_pattern
-- name    : VWZClique.fold_to_smaller_pattern
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T01:02:23.258462+00:00
-- url     : https://prove2.me/theorems/b8945f99-a766-4b92-bd57-4411d54e90ff
-- title:
--   Lemma 3.2 — Edge loss and transformed weight tables
-- statement:
--   A single shared arithmetic program constructs all weights of a nine-position pattern in quadratic arithmetic cost. One binary factor is saved per active wedge, and the transformed weighted sum equals the partial-swap contribution on every input.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Lemma 3.2. https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_FoldedSum

open VWZClique OAI.MatrixMultiplication.Arithmetic

theorem VWZClique.fold_to_smaller_pattern :
    ∃ C : ℕ, ∀ (F : Type*) [Field F] [CharZero F] (L : ℕ)
      (E : Finset EdgeSlot) (a b : Option (Mask L)),
      (a.isSome = true → wedgePlaced E 0 2) →
      (b.isSome = true → wedgePlaced E 1 0) →
      ∃ (H : SimpleGraph V) (r : ℕ) (P : Program F (ChannelKey L) r)
        (out : WeightKey (2^L) → Fin r),
        (Nat.card H.edgeSet + a.isSome.toNat + b.isSome.toNat ≤ E.card) ∧
        P.cost ≤ C * (2^L)^2 ∧ ∀ w,
          weightedSum H (fun i => P.eval w (out i)) = placedFold E a b w := by sorry
