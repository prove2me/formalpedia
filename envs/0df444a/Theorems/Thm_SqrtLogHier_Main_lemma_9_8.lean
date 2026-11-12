-- Prove2me | Theorems.Thm_SqrtLogHier_Main_lemma_9_8
-- name    : SqrtLogHier.Main.lemma_9_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:58:01.891868+00:00
-- url     : https://prove2.me/theorems/d631443b-efa2-4218-ad72-c6127aafeed5
-- title:
--   Lemma 9.8 — common substrings of A and B counted through the distinct substrings of A#B
-- statement:
--   Let $A,B$ be strings and $\#$ a symbol occurring in neither of them. With $F(X)$ the set of nonempty substrings of $X$ and $D(X)=|F(X)|$ (Definition 9.7),
--
--   $$|F(A)\cap F(B)|=D(A)+D(B)+(|A|+1)(|B|+1)-D(A\#B).$$
--
--   This is Lemma 9.8 of the paper (p. 54); it reduces Dictionary Matching to Distinct Substring Counting (Theorem 9.9).
--
--   Differences from the source:
--   - encoding: |F(A) ∩ F(B)| = D(A) + D(B) + (|A| + 1)(|B| + 1) − D(A#B) → the same identity in ℤ, with F as a set of lists and D = Set.ncard; reason: avoids truncated subtraction in ℕ; the sets are finite
-- source:
--   Kempa, Kociumaka, A Unified and Robust Theory of Lower and Upper Bounds for the √log n Barrier, STOC 2027 submission (manuscript sha256 7a17340d…), p. 54, Lemma 9.8

import Mathlib
import Definitions.Def_SqrtLogHier_Main_StringArrays

set_option autoImplicit false

namespace SqrtLogHier.Main

/-- Lemma 9.8 (p. 54): for strings `A, B` and a symbol `#` occurring in neither,
`|F(A) ∩ F(B)| = D(A) + D(B) + (|A| + 1)(|B| + 1) − D(A#B)`. -/
theorem lemma_9_8 {β : Type} (A B : List β) (sharp : β) (hA : sharp ∉ A) (hB : sharp ∉ B) :
    ((substrs A ∩ substrs B).ncard : ℤ) =
      distinctCount A + distinctCount B + (A.length + 1) * (B.length + 1) -
        distinctCount (A ++ sharp :: B) := by sorry

end SqrtLogHier.Main
