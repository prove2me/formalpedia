-- Prove2me | Theorems.Thm_VWZClique_basis_transform
-- name    : VWZClique.basis_transform
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T01:03:44.798812+00:00
-- url     : https://prove2.me/theorems/ca86a5a4-6a98-4027-b268-e3bdbc0596db
-- title:
--   Lemma 3.3 — Cost of the product-basis transform
-- statement:
--   A single arithmetic program evaluates all product-basis inner products using $O((L+1)4^L)$ operations on $4^L$ inputs.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Section 4, conclusion of the proof of Lemma 3.3. https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_Operators
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

open VWZClique OAI.MatrixMultiplication.Arithmetic

theorem VWZClique.basis_transform :
    ∃ C : ℕ, ∀ (F : Type*) [Field F] [CharZero F] (L : ℕ),
      ∃ (r : ℕ) (P : Program F (PairBits L) r) (out : BasisLabel L → Fin r),
        P.cost ≤ C * (L + 1) * 4^L ∧ ∀ (w : PairBits L → F) j,
          P.eval w (out j) = ∑ x, (basisEntry j x : F) * w x := by sorry
