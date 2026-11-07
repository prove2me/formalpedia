-- Prove2me | Theorems.Thm_RevisitXor_lemma_6_increments
-- name    : RevisitXor.lemma_6_increments
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:25.153208+00:00
-- url     : https://prove2.me/theorems/283e3e58-0fe8-4b25-8f25-b0cc53fae5eb
-- title:
--   Lemma 6 (increments): $|W_i-\mathbb E[W_i]|\le c$ and $\operatorname{var}W_i\le c/(M-2(i-1))$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $M=2^m$, $h:[2]^{2m}\to[2]$, $1\le i\le M/2$, and condition on any fixed outcome $x_{<i}$ of $X_{<i}$. The variable
--
--   $$W_i:=\mathbb E_{X_{>i}}\,w(x_1,\dots,x_{i-1},X_i,X_{i+1},\dots,X_{M/2})$$
--
--   (a function of the next edge $X_i$) satisfies
--
--   1. boundedness: $|W_i-\mathbb E[W_i]|\le c$ for every value of $X_i$;
--   2. variance bound: $\operatorname{var}W_i\le c/(M-2(i-1))$.
--
--   These are the two inputs of the method of bounded variances; the variances sum harmonically to $O(\log M)$.
--
--   **Formalization Note** $\mathbb E[W_i]$ and $\operatorname{var}W_i$ are over $X_i$ uniform among the pairs of the uncovered set $R$. The outcome $x_{<i}$ is the prefix of a valid sequence. $M-2(i-1)\ge2$ is computed in the reals.
--
--   Differences from the source:
--   - encoding: conditioned on any fixed outcome x_{<i} of X_{<i} → the first i − 1 edges of any valid sequence ys, with X_i ranging over the pairs of the remaining set; reason: every valid prefix extends to a valid sequence, and under the uniform law X_i given x_{<i} is uniform on those pairs
--   - encoding: the c of both items → one absolute c > 0 chosen before m, h, i and the outcome; reason: p.1 convention
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Lemma 6, p.7

import Mathlib
import Definitions.Def_RevisitXor_Wi

namespace RevisitXor

/-- **Lemma 6, boundedness and variance.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), Lemma 6, p.7: "Also, conditioned on any fixed outcome x<i of X<i, the variable
Wi := E_{X>i} w(x1, x2, . . . , xi−1, Xi, Xi+1, . . . , XM/2) enjoys: 1. Boundedness:
|Wi − E[Wi]| := b ≤ c, 2. Variance bound: varWi := vi ≤ c/(M − 2(i − 1))."

**Formalization Note.** One absolute `c > 0`, chosen before `m`, `h`, `i` and the outcome. The
outcome `x_{<i}` is the first `i - 1` edges of a valid sequence `ys` (every valid prefix extends to
one); `i` is 1-based, `1 ≤ i ≤ M/2`. `W_i`, `E[W_i]` and `var W_i` are over the next edge `X_i = e`,
uniform among the pairs of the remaining set `R` (`Wi`, `EWi`, `varWi`). `M - 2(i - 1)` is computed
in ℝ (it is `≥ 2`). For `m = 0` there is no `i` and the statement is vacuous. -/
theorem lemma_6_increments :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, ∀ h : Cube m × Cube m → ZMod 2, ∀ ys ∈ validSeqs m,
      ∀ i : ℕ, 1 ≤ i → i ≤ 2 ^ m / 2 →
        (∀ e ∈ pairsIn (remaining ys i), |Wi h ys i e - EWi h ys i| ≤ c) ∧
          varWi h ys i ≤ c / ((2 : ℝ) ^ m - 2 * ((i : ℝ) - 1)) := by sorry

end RevisitXor
