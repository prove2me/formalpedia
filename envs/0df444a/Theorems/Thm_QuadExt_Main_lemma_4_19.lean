-- Prove2me | Theorems.Thm_QuadExt_Main_lemma_4_19
-- name    : QuadExt.Main.lemma_4_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:44.714129+00:00
-- url     : https://prove2.me/theorems/d9cedcc9-5123-4159-9ee9-51092d882957
-- title:
--   Lemma 4.19 — $q$-purity survives composing the generating map with an injective affine map
-- statement:
--   Let $X = f(U_s)$ be a quadratic source that is $q$-pure, and let $L : \mathbb F_2^r \to \mathbb F_2^s$ be an injective affine map. Then the source
--   $$X' = (f \circ L)(U_r)$$
--   is also $q$-pure. Restricting the generating bits of a pure quadratic source to an affine subspace therefore keeps it pure; the proof of Theorem 7.2 uses this after each such restriction.
--
--   Differences from the source: none.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 17 (PDF 18), Lemma 4.19

import Mathlib
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Pure

namespace QuadExt.Main

/-- **Lemma 4.19** (p. 17): if the quadratic source `f(U_s)` is `q`-pure, then so is `(f ∘ L)(U_r)`
for every injective affine `L : 𝔽₂^r → 𝔽₂^s`. -/
theorem lemma_4_19 (n s r : ℕ) (q : ℝ) (f : (Fin s → ZMod 2) → (Fin n → ZMod 2))
    (hf : IsQuadraticMap f) (hpure : IsPure q f)
    (L : (Fin r → ZMod 2) → (Fin s → ZMod 2)) (hL : IsInjAffine L) :
    IsPure q (f ∘ L) := by sorry

end QuadExt.Main
