-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_lemma_5_8
-- name    : ShiAuthentication.BA.Supplement.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:29:15.144569+00:00
-- url     : https://prove2.me/theorems/c28f3036-08a0-4581-a3f1-9e03786fcd81
-- title:
--   Lemma 5.8 — common in-neighbours of nonadjacent receivers
-- statement:
--   Let $S$ be the designated sender and suppose $t\le n-2$ and $n\le 2t$. Let $G$ be a public authentication graph on which $\mathrm{BB}(G,S,t)$ is feasible. Then for every nonadjacent pair of receivers $a,b\neq S$ (distinct, with neither $a\to b$ nor $b\to a$), at least
--   $$d=2t-n+1$$
--   receivers $z\neq S$ satisfy $z\to a$ and $z\to b$.
--
--   With Lemma 5.9 this gives the $\Omega_\alpha(n^2)$ lower bound on $A_{BB}(n,\lfloor\alpha n\rfloor)$ for a dishonest-majority fraction $\alpha\in(1/2,1)$.
--
--   Differences from the source:
--   - encoding: BB(G, S, t) feasible → BBPossible .publicGraph t G S; reason: Definition 3.1 in the model of §3.1, where the authentication graph G is public
--   - encoding: t ≤ n − 2 → t + 2 ≤ n; reason: avoids truncated natural subtraction; equivalent for n ≥ 2, which n ≤ 2t ≤ 2n − 4 forces
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 5.8, p. 33

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Lemma 5.8**, p. 33. If `t ≤ n − 2` and `n ≤ 2t`, then for every nonadjacent pair of
receivers `a, b` (`a, b ≠ S`) in a graph `G` with `BB(G, S, t)` feasible (public authentication
graph), at least `d = 2t − n + 1` receivers `z ≠ S` satisfy `z → a` and `z → b`. -/
theorem lemma_5_8 (n t : ℕ) (htn : t + 2 ≤ n) (hn2t : n ≤ 2 * t) (G : AuthGraph n) (S : Fin n)
    (hBB : BBPossible .publicGraph t G S) (a b : Fin n) (haS : a ≠ S) (hbS : b ≠ S)
    (hab : Nonadjacent G a b) :
    2 * t - n + 1 ≤
      (Finset.univ.filter (fun z => z ≠ S ∧ G.adj z a = true ∧ G.adj z b = true)).card := by sorry

end ShiAuthentication.BA.Supplement
