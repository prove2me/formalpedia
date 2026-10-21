-- Prove2me | Theorems.Thm_SparseReznick_Psatz_lemma_3_1
-- name    : SparseReznick.Psatz.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:47.675789+00:00
-- url     : https://prove2.me/theorems/ce072b76-1e32-4747-abd1-78c0531b4959
-- title:
--   Lemma 3.1 — the preordering positivity criterion
-- statement:
--   Let $A$ be a commutative $\mathbb Q$-algebra with a preordering $T$. Assume every element $h\in A$ is arithmetically bounded: some natural $K$ satisfies $K+h,K-h\in T$. If $f\in A$ is strictly positive under every real ring homomorphism nonnegative on $T$, then
--
--   $$f\in T.$$
--
--   This is the paper’s ring-level criterion used in its uniform-denominator argument. The spectrum is represented by real-valued ring homomorphisms, as on the cited page.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, p. 9, Lemma 3.1

import Mathlib
import Definitions.Def_SparseReznick_Psatz_Preordering

namespace SparseReznick.Psatz

theorem lemma_3_1 {A : Type*} [CommRing A] [Nontrivial A] [Algebra ℚ A]
    (T : Preordering A) (hT : IsArithBounded T) (f : A)
    (hf : ∀ φ ∈ Sper T, 0 < φ f) : f ∈ T.carrier := by sorry

end SparseReznick.Psatz
