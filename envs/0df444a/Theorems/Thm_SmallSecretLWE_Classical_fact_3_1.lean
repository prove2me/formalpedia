-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_fact_3_1
-- name    : SmallSecretLWE.Classical.fact_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:26:28.071812+00:00
-- url     : https://prove2.me/theorems/2d6dab56-05a2-4d18-a380-553a5db2d3da
-- title:
--   Fact 3.1 — the collision probability of $L$ i.i.d. draws is minimized by the uniform law
-- statement:
--   Let $S$ be a finite set, $\mathcal D$ a distribution on $S$ and $L\in\mathbb N$. Then
--   $$\Pr_{X_1,\dots,X_L\overset{iid}{\sim}\mathcal D}[\exists\text{ collision}]\ \ge\ \Pr_{X_1,\dots,X_L\overset{iid}{\sim}\mathrm{Unif}(S)}[\exists\text{ collision}]\ =\ 1-\prod_{j=1}^{L-1}\Big(1-\frac{j}{|S|}\Big),$$
--   where a collision is a pair $i\neq i'$ with $X_i=X_{i'}$. It is the birthday bound behind Proposition 4.4.
--
--   Differences from the source:
--   - reading: 'and $k\in\mathbb N$' → $L\in\mathbb N$; reason: obvious typo: the statement uses $L$ and never $k$
--   - encoding: finite set $S$, distribution $\mathcal D$, probability of a collision → `[Fintype S]`, `D : PMF S`; sums over `x : Fin L → S` of $\prod_i\mathcal D(x_i)$ (resp. $|S|^{-L}$) over non-injective `x`; reason: same quantities
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 11, Fact 3.1

import Mathlib

open scoped Classical

namespace SmallSecretLWE.Classical

/-- Fact 3.1. For every finite set `S`, distribution `D` on `S` and `L ∈ ℕ`, the probability of a
collision among `L` i.i.d. draws from `D` is at least the probability of a collision among `L`
i.i.d. uniform draws from `S`, which equals `1 − Π_{j=1}^{L−1} (1 − j/|S|)`. -/
theorem fact_3_1 {S : Type*} [Fintype S] (D : PMF S) (L : ℕ) :
    (∑ x : Fin L → S, if ¬ Function.Injective x then ((1 : ℝ) / Fintype.card S) ^ L else 0) ≤
      (∑ x : Fin L → S, if ¬ Function.Injective x then ∏ i, (D (x i)).toReal else 0) ∧
    (∑ x : Fin L → S, if ¬ Function.Injective x then ((1 : ℝ) / Fintype.card S) ^ L else 0) =
      1 - ∏ j ∈ Finset.Icc 1 (L - 1), (1 - (j : ℝ) / Fintype.card S) := by sorry

end SmallSecretLWE.Classical
