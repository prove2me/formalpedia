-- Prove2me | Theorems.Thm_RevisitXor_eq_3
-- name    : RevisitXor.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:18.81638+00:00
-- url     : https://prove2.me/theorems/0d2208d8-ee4c-4db0-9f16-bc1acb9a7aa7
-- title:
--   Expression (3) for $W_i$
-- statement:
--   Let $M=2^m$, $h:[2]^{2m}\to[2]$, $1\le i\le M/2$, fix an outcome $x_{<i}$, and let $R$ be the set of $r=M-2(i-1)$ vertices not touching $x_{<i}$.
--
--   1. If $r=2$ then $W_i$ is constant: it equals $\mathbb E[W_i]$ for the only pair of $R$.
--   2. If $r\ge4$, write $X_i=\{U,V\}$ and let $w(x)=\sum_{y\in R}w(\{x,y\})$ be the sum of the weights of the edges touching $x$. Then
--   $$W_i=w(x_1,\dots,x_{i-1})+w(X_i)+\frac1{r-3}\Big(\sum_{\{x,y\}\subseteq R}w(\{x,y\})-w(U)-w(V)+w(X_i)\Big), \tag{3}$$
--   because after $X_i$ is selected each remaining edge of $R$ is chosen with probability $1/(r-3)$.
--
--   Expression (3) separates $W_i$ into a part depending on $x_{<i}$ only and the part $Y_i=\frac1{r-3}((r-2)w(X_i)-w(U)-w(V))$ that carries the randomness of $X_i$.
--
--   **Formalization Note** The outcome $x_{<i}$ is the prefix of a valid sequence; $\sum_{\{x,y\}\subseteq R}$ runs over 2-element subsets.
--
--   Differences from the source:
--   - encoding: Σ_{{x,y}⊆R} w(x, y) → the sum of w({x, y}) over the 2-element subsets of R (pairsIn R); reason: the paper's w(x, y) inside the sum denotes w({x, y})
--   - encoding: r = 2, r ≥ 4 with r = M − 2(i − 1) → M = 2 + 2(i − 1) and 4 + 2(i − 1) ≤ M in ℕ; r computed in ℝ inside (3); reason: same cases; avoids truncated subtraction
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), proof of Lemma 6, (3), p.8

import Mathlib
import Definitions.Def_RevisitXor_Wi

namespace RevisitXor

/-- **Expression (3) for `W_i`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), proof of Lemma 6, (3), p.8: "Let R be the remaining set of r = M − 2(i − 1) nodes not touching x<i.
If r = 2 then Wi is constant and the desired bounds are immediate; so let r ≥ 4. Write Xi = {U, V}.
Let w(x) := Σ_{y∈R} w({x, y}) be the sum of the weights of the edges touching x. We can write
Wi = w(x1, . . . , xi−1) + w(Xi) + 1/(r − 3) (Σ_{{x,y}⊆R} w(x, y) − w(U) − w(V) + w(Xi)), (3)
because after Xi is selected each remaining edge is chosen with prob. 1/(r − 3)."

**Formalization Note.** The outcome `x_{<i}` is the first `i - 1` edges of a valid sequence `ys`
(`i` 1-based, `1 ≤ i ≤ M/2`), and `R = remaining ys i`. Both cases of the text are stated: if
`r = 2` then `W_i` is constant over the next edge (it equals `E[W_i]`); if `r ≥ 4` then for every pair
`X_i = {U, V}` of `R`, (3) holds. `r = M − 2(i − 1)` is compared in ℕ (`M = 2 + 2(i − 1)`,
`4 + 2(i − 1) ≤ M`) and computed in ℝ inside (3). `Σ_{{x,y}⊆R}` runs over the 2-element subsets of
`R` (`pairsIn R`), and `w(x, y)` there is `w({x, y})`. -/
theorem eq_3 {m : ℕ} (h : Cube m × Cube m → ZMod 2) (ys : Fin (2 ^ m / 2) → Sym2 (Cube m))
    (hys : ys ∈ validSeqs m) (i : ℕ) (hi : 1 ≤ i) (hiM : i ≤ 2 ^ m / 2) :
    (2 ^ m = 2 + 2 * (i - 1) →
      ∀ e ∈ pairsIn (remaining ys i), Wi h ys i e = EWi h ys i) ∧
    (4 + 2 * (i - 1) ≤ 2 ^ m → ∀ U V : Cube m, s(U, V) ∈ pairsIn (remaining ys i) →
      Wi h ys i s(U, V) =
        (∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ m / 2) => j.val + 1 < i), wEdge h (ys j)) +
          wEdge h s(U, V) +
          1 / (((2 : ℝ) ^ m - 2 * ((i : ℝ) - 1)) - 3) *
            (∑ p ∈ pairsIn (remaining ys i), wEdge h p -
              ∑ y ∈ remaining ys i, wEdge h s(U, y) -
              ∑ y ∈ remaining ys i, wEdge h s(V, y) + wEdge h s(U, V))) := by sorry

end RevisitXor
