-- Prove2me | Theorems.Thm_RainsSep_Distill_coefficient_lp_tends_to_zero
-- name    : RainsSep.Distill.coefficient_lp_tends_to_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:37.012956+00:00
-- url     : https://prove2.me/theorems/e17d3689-a756-4dad-96df-6b1009cdf951
-- title:
--   Eqs. (42)–(45): the binomial estimate, stated uniformly in the coefficients
-- statement:
--   Let $\tfrac12\le f\le1$ and $R>1-H_2(f)$, where $H_2$ is the binary entropy in bits. For every $\varepsilon>0$ there is $N$ such that for every $n\ge N$ and every real vector $(b_0,\dots,b_n)$ with
--
--   $$
--   0\le b_i\le\binom ni3^i\quad(0\le i\le n)\qquad\text{and}\qquad \sum_{i=0}^n b_i\Big(\frac12\Big)^{n-i}\Big(\frac16\Big)^i\le 2^{-nR},
--   $$
--
--   we have
--
--   $$
--   \sum_{i=0}^n b_i\,f^{n-i}\Big(\frac{1-f}{3}\Big)^i\le\varepsilon .
--   $$
--
--   With $b_i=B_i(\mathcal P)$, the first constraint is Eq. (34) and the second is $B(\tfrac12,\tfrac16)\le 1/K$ (Eq. (36)) with $K\ge 2^{nR}$; the conclusion says the output fidelity $B(f,\tfrac{1-f}{3})$ is small. This is the rigorous content of the estimate in the proof of Theorem 2.
--
--   Differences from the source:
--   - reading: the heuristic estimate (42)–(45) with ≃, ≳ and "for some j" → a bound uniform in every coefficient vector b satisfying (34) and B(1/2, 1/6) ≤ 2^(−nR), with an explicit ε–N quantifier; reason: this is the precise statement the estimate establishes; the feasible region is exactly the constraints the proof uses
--   - reading: f ≥ 1/2 → 1/2 ≤ f ≤ 1; reason: f is the fidelity of a state, so f ≤ 1
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, proof of Theorem 2, Eqs. (42)–(45), p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information

open QAlgorithms

namespace RainsSep.Distill

/-- **The binomial estimate behind Eqs. (42)–(45).**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, proof of Theorem 2, Eqs. (42)–(45), p. 4: "For a fixed value of B(f, (1−f)/3), the lowest
possible value of B(1/2, 1/6) (ignoring all other constraints) is attained when the weight of the
B_i is concentrated at low i … B(f, (1−f)/3) ≃ Σ_{0≤i<j} (n choose i) f^{n−i}(1 − f)^i (42) for
some j. In order for this not to tend to 0 as n increases, we must have j ≳ n(1 − f). But then
B(1/2, 1/6) ≃ 2^{−n} Σ_{0≤i<j} (n choose i), (43) so B(1/2, 1/6) ≃ 2^{n(H2(j/n)−1)} ≳
2^{n(H2(f)−1)}. (44) On the other hand, by (36), we know B(1/2, 1/6) ≤ 1/K. But then
log2(K)/n ≲ 1 − H2(f). (45)"

Let `1/2 ≤ f ≤ 1` and `R > 1 − H₂(f)`. For every `ε > 0` there is `N` such that for every
`n ≥ N` and every coefficient vector `b_0, …, b_n` with `0 ≤ b_i ≤ C(n, i)·3^i` (Eq. (34)) and
`Σ_i b_i (1/2)^{n−i} (1/6)^i ≤ 2^{−nR}` (the bound `B(1/2, 1/6) ≤ 1/K` with `K ≥ 2^{nR}`),
`Σ_i b_i f^{n−i} ((1 − f)/3)^i ≤ ε`.

**Formalization Note.** This is the precise content of the heuristic steps (42)–(45): the
`≃`, `≳` and "for some j" are replaced by a bound uniform in the coefficient vector `b`.
`H₂` is `binEntropy2` (bits, `0 log 0 = 0`); `2^{−nR}` is a real power. -/
theorem coefficient_lp_tends_to_zero (f : ℝ) (hf0 : 1 / 2 ≤ f) (hf1 : f ≤ 1) (R : ℝ)
    (hR : 1 - binEntropy2 f < R) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ b : ℕ → ℝ,
      (∀ i ≤ n, 0 ≤ b i ∧ b i ≤ (n.choose i : ℝ) * 3 ^ i) →
      ∑ i ∈ Finset.range (n + 1), b i * (1 / 2 : ℝ) ^ (n - i) * (1 / 6 : ℝ) ^ i ≤
        (2 : ℝ) ^ (-((n : ℝ) * R)) →
      ∑ i ∈ Finset.range (n + 1), b i * f ^ (n - i) * ((1 - f) / 3) ^ i ≤ ε := by sorry

end RainsSep.Distill
