-- Prove2me | Theorems.Thm_SqrtLogHier_Main_lemma_9_4
-- name    : SqrtLogHier.Main.lemma_9_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:57:37.769199+00:00
-- url     : https://prove2.me/theorems/0379aeb1-7d34-48a0-a7fe-f264deaa0614
-- title:
--   Lemma 9.4 — a de Bruijn gadget whose shortest unique substrings are the absent length-k strings of T
-- statement:
--   Let $\Sigma$ be an alphabet of size $\sigma\ge2$, $\#\notin\Sigma$, $T\in\Sigma^*$ and $k\ge1$. Let $B_k$ be any de Bruijn sequence of order $k$ over $\Sigma$, $P$ and $S$ its prefix and suffix of length $k-1$, $Z=\#^k$, $D=ZPZSZ$ and
--
--   $$U_k=Z\,B_k\,Z\,T\,Z\,T\,Z\,D\,D.$$
--
--   Then $U_k$ has no unique substring of length less than $k$, and its unique substrings of length $k$ are exactly the strings of $\Sigma^k$ that do not occur in $T$.
--
--   This is Lemma 9.4 of the paper (p. 51); it drives the reduction from Shortest Absent Substring to Shortest Unique Substring (Theorem 9.5).
--
--   Differences from the source:
--   - encoding: an alphabet Σ of size σ ≥ 2 and a symbol # ∉ Σ; T ∈ Σ*; B_k a de Bruijn sequence of order k over Σ (Definition 4.11 over [0..σ)) → Σ a finite type α with Fintype.card α ≥ 2; U_k a string over Option α with # = none and the symbols of Σ as some a; IsDeBruijn k B over α; reason: the fresh symbol made explicit; Definition 4.11 transported to any alphabet of size σ
--   - encoding: a unique substring (a substring with exactly one occurrence) → a string V with occ V U = 1 (occ counts starting positions; the empty string has |U| + 1 occurrences); reason: the empty string is never unique, so whether it counts as a substring changes nothing
-- source:
--   Kempa, Kociumaka, A Unified and Robust Theory of Lower and Upper Bounds for the √log n Barrier, STOC 2027 submission (manuscript sha256 7a17340d…), p. 51, Lemma 9.4

import Mathlib
import Definitions.Def_SqrtLogHier_Main_StringArrays

set_option autoImplicit false

namespace SqrtLogHier.Main

/-- Lemma 9.4 (p. 51): with `# = none` outside the alphabet `Σ = α` (`|Σ| ≥ 2`), any de Bruijn
sequence `B_k` of order `k ≥ 1` over `Σ`, its prefix `P` and suffix `S` of length `k − 1`,
`Z = #^k`, `D = Z P Z S Z` and `U_k = Z B_k Z T Z T Z D D`: `U_k` has no unique substring of length
less than `k`, and its unique substrings of length `k` are exactly the strings of `Σ^k` that do
not occur in `T`. -/
theorem lemma_9_4 {α : Type} [Fintype α] [DecidableEq α] (hσ : 2 ≤ Fintype.card α)
    (T : List α) (k : ℕ) (hk : 1 ≤ k) (B : List α) (hB : IsDeBruijn k B) :
    let Z : List (Option α) := List.replicate k none
    let P := B.take (k - 1)
    let S := B.drop (B.length - (k - 1))
    let D := Z ++ P.map some ++ Z ++ S.map some ++ Z
    let U := Z ++ B.map some ++ Z ++ T.map some ++ Z ++ T.map some ++ Z ++ D ++ D
    (∀ V : List (Option α), occ V U = 1 → k ≤ V.length) ∧
    ∀ V : List (Option α), V.length = k →
      (occ V U = 1 ↔ ∃ V' : List α, V = V'.map some ∧ ¬ V' <:+: T) := by sorry

end SqrtLogHier.Main
