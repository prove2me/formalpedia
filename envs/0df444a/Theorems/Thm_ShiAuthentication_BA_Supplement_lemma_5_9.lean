-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_lemma_5_9
-- name    : ShiAuthentication.BA.Supplement.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:26:58.374563+00:00
-- url     : https://prove2.me/theorems/d68092d5-7407-4756-8093-67bacb573093
-- title:
--   Lemma 5.9 — counting receiver authentication edges
-- statement:
--   Let $S$ be the designated sender and $U\subseteq P\setminus\{S\}$ a set of $N\ge1$ receivers, and let $d$ be an integer with $0\le d\le N-1$. Suppose that for every nonadjacent pair $a,b\in U$ (distinct, with neither $a\to b$ nor $b\to a$) at least $d$ receivers $z\in U$ satisfy $z\to a$ and $z\to b$. Then
--   $$\sum_{v\in U}|K_v\cap U|\ \ge\ dN-\binom{d+1}{2}\ =\ \binom{N}{2}-\binom{N-d}{2},$$
--   where $K_v$ is the set of parties whose keys are initially authenticated to $v$.
--
--   This edge count, applied to all receivers, gives the quadratic broadcast lower bounds in the dishonest-majority regime (Main Theorem 3) and at maximum resilience (Theorem 5.10).
--
--   Differences from the source:
--   - encoding: 0 ≤ d ≤ N − 1 and the displayed (in)equalities → d + 1 ≤ N in ℕ; both sides computed in ℤ; reason: avoids truncated natural subtraction; the values are unchanged
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 5.9, p. 33

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Lemma 5.9 (Counting receiver authentication edges)**, p. 33. Let `U ⊆ R = P \ {S}` be a set
of `N ≥ 1` receivers and `d` an integer with `0 ≤ d ≤ N − 1`. If for every nonadjacent pair
`a, b ∈ U` at least `d` receivers `z ∈ U` satisfy `z → a` and `z → b`, then
`Σ_{v∈U} |K_v ∩ U| ≥ dN − C(d+1, 2)`, and `dN − C(d+1, 2) = C(N, 2) − C(N − d, 2)`
(both computed in `ℤ`). -/
theorem lemma_5_9 (n : ℕ) (G : AuthGraph n) (S : Fin n) (U : Finset (Fin n)) (hSU : S ∉ U)
    (N d : ℕ) (hUN : U.card = N) (hN : 1 ≤ N) (hd : d + 1 ≤ N)
    (hcommon : ∀ a ∈ U, ∀ b ∈ U, Nonadjacent G a b →
      d ≤ (U.filter (fun z => G.adj z a = true ∧ G.adj z b = true)).card) :
    (d : ℤ) * N - ((d + 1).choose 2 : ℕ) ≤ ∑ v ∈ U, ((G.signersOf v ∩ U).card : ℤ) ∧
    (d : ℤ) * N - ((d + 1).choose 2 : ℕ) = ((N.choose 2 : ℕ) : ℤ) - ((N - d).choose 2 : ℕ) := by sorry

end ShiAuthentication.BA.Supplement
