-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_Supplement_lemma_4_2
-- name    : TreeOrient.RecGreedy.Supplement.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:55:04.338819+00:00
-- url     : https://prove2.me/theorems/152717a8-95e1-4a39-9280-a798897b31f3
-- title:
--   Lemma 4.2 (corrected: RG-DC guesses from 0, D₁(v) kept) — RG-DC returns a feasible length-respecting T with f_X(T) ≥ f_X(T∗)/i
-- statement:
--   Consider an instance of submodular tree orienteering with length constraints: $n$ vertices, nonnegative integer edge costs $c$ and edge lengths $\ell$, and a monotone submodular reward $f$ with natural values. Fix a root $r$, an offset $k_r$ (the length from $r^*$ to $r$), responsibilities $Y$, length bounds $D(w)$ for $w\in Y$, a cost budget $B$, a length bound $L$, a set $X$ of already covered vertices and a depth $i\ge1$, and write $f_X(T)=f(V(T)\cup X)-f(X)$.
--
--   Let $T^*$ be an arborescence compatible with $RG\text{-}DC(r,k_r,Y,D,B,L,X,i)$: it is $r$-rooted, visits every vertex of $Y$, has $l_{T^*}(w)\le D(w)$ for every $w\in Y\setminus\{r\}$, has at most $(3/2)^i$ non-root vertices, cost at most $B$, and
--
--   $$\sum_{w\in V(T^*)\setminus\{r\}}\bigl(k_r+l_{T^*}(w)\bigr)\le L .$$
--
--   Then Algorithm 3, $RG\text{-}DC(r,k_r,Y,D,B,L,X,i)$, returns an edge set $T$ (not Infeasible) such that
--
--   1. every vertex of $T$ is reachable from $r$, $c(T)\le B$ and $Y\subseteq V(T)$;
--   2. $T$ contains an $r$-rooted arborescence on the vertex set $V(T)$ whose length sum (with offset $k_r$) is at most $L$ and which satisfies the bounds $D$ on $Y\setminus\{r\}$;
--   3. $$f_X(T)\ \ge\ \frac{f_X(T^*)}{i}.$$
--
--   The lemma holds for all values of $k_r$, $D$, $B$ and $L$, not only at the top-level call; with Proposition 4.1 it gives Theorem 4.3.
--
--   **Formalization Note** $l_T(w)$ is the least length of an $r$–$w$ walk in $T$, which in an arborescence is the length of the unique path. The algorithm is `rgdc I 1 .enum`; its conventions are those of `TreeOrient.RecGreedy.Supplement.LengthModel`.
--
--   Differences from the source:
--   - correction: Algorithm 3 guesses $B_1$, $L_1$, $d_1$ from $1$ and sets $D_2=D-d_1$ → the guesses start at $0$, and a guess with $d_1>D(w)$ for some $w\in Y\setminus(S\cup\{v\})$ is skipped; reason: with zero costs the printed lemma fails: take $f(S)=|S|$, $c\equiv0$, $B=0$, $X=Y=\emptyset$, $i=2$ and $T^*$ a two-edge path from $r$; the loop "for $1\le B_1\le B$" is empty, so the printed procedure returns $\emptyset$ with $f_X(\emptyset)=1<3/2=f_X(T^*)/2$. Zero lengths need $L_1=0$ and $d_1=0$ in the same way, and the skip keeps $D_2$ nonnegative where the printed $D(w)-d_1<0$ leaves no feasible right subtree.
--   - correction: Algorithm 3, lines 16–17, set $D_1=D$ on $S$ and $D_1(v)=\min\{d_1,D_1(v)\}$, which forgets $D(v)$ when the separator $v$ lies in $Y\setminus S$ → $D_1(v)=\min\{d_1,D(v)\}$ whenever $v\in Y$; reason: with the printed rule the output can violate $D$, which the parameter description on p. 11 requires of every returned arborescence: costs $1$, $B=2$, $L=10$, $\ell(r,u)=\ell(u,v)=\ell(v,x)=1$, $\ell(r,v)=3$, other lengths $100$, $Y=\{v\}$, $D(v)=2$, $k_r=0$, $X=\emptyset$, $i=2$, $f(S)=|S\cap\{u,v\}|+2|S\cap\{x\}|$; the guess $(v,S=\emptyset,B_1=1,L_1=3,d_1=3)$ yields $\{(r,v),(v,x)\}$ with $f_X=3$, the largest value of any candidate, and every candidate of that value reaches $v$ at length $3>D(v)$. The correct guess of the proof has $v\in S$, so no guess the proof uses is lost.
--   - reading: $\sum_{v\in T^*}(k_r+l_{T^*}(v))\le L$ → the sum over the non-root vertices of $T^*$; reason: the base case of Algorithm 3 charges only $k_r+\ell(r,v)$ for the edge $(r,v)$, and counting the root of $T_2^*$ (the separator $v$, already counted in $T_1^*$) would make (8) false.
--   - encoding: "the arborescence returned by RG-DC" → the call returns some edge set $T$ satisfying 1 and 2; reason: the lemma presupposes a return; $T_1\cup T_2$ may share vertices, so the length bounds are stated on a contained arborescence.
--   - encoding: the dictionary $D$ on $Y$ → a total function $D$ on vertices; reason: only its values on $Y\setminus\{r\}$ are read.
--   - encoding: $\ell:E\to\mathbb Z_+$ and $f:2^V\to\mathbb R_+$ → natural-valued lengths (zero allowed) and natural-valued $f$; reason: the published model's conventions for costs and the oracle; Algorithm 3 with enumeration only compares values of $f$.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, pp. 11–13 (PDF 12–14), Lemma 4.2 and its proof; Algorithm 3, p. 12 (PDF 13); parameters of RG-DC, p. 11 (PDF 12)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Supplement_LengthModel

namespace TreeOrient.RecGreedy.Supplement

/-- Lemma 4.2, p. 11 (PDF 12): `RG-DC(r, k_r, Y, D, B, L, X, i)` returns a feasible,
length-respecting output `T` with `f_X(T) ≥ f_X(T∗)/i` for every compatible `T∗`. -/
theorem lemma_4_2 {n : ℕ} (I : LInst n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n))
    (D : Fin n → ℕ) (B L : ℕ) (X : Finset (Fin n)) (i : ℕ) (A : Edges n)
    (hmono : IsMonotone I.f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)))
    (hi : 1 ≤ i)
    (hA : CompatibleDC I r kr Y D B L ((3 / 2 : ℝ) ^ i) A) :
    ∃ T, (rgdc I 1 .enum i r kr Y D B L X).1 = some T ∧
      FeasibleDC I r kr Y D B L T ∧
      fX I.f X r A ≤ (i : ℝ) * fX I.f X r T := by sorry

end TreeOrient.RecGreedy.Supplement
