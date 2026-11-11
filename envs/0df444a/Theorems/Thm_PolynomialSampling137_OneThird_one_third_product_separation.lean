-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_one_third_product_separation
-- name    : PolynomialSampling137.OneThird.one_third_product_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T10:26:43.908568+00:00
-- url     : https://prove2.me/theorems/53cf1320-2d2d-4553-b7ef-208f8537de3e
-- title:
--   Theorem 4 — one-third product separation, including bounded degree-d rank
-- statement:
--   For each integer $d\ge1$ there is a family of positive uniform acceptance gaps $\delta_{d,r}\le1/3$ for every integer $r\ge1$. Each witness satisfies Theorem 1's bounded-rank acceptance-gap property and, for every $s,n\ge0$ and every map $Q:\mathbb F_2^s\to\mathbb F_2^n$ with $\operatorname{rank}_d(Q_i)\le r$ in every coordinate,
--
--   $$\operatorname{Ov}(Q(U_s),\operatorname{Ber}(1/3)^{\otimes n})\le\exp(-\delta_{d,r}^{\,6}n).$$
--
--   With the same rank-one witness $\delta_d=\delta_{d,1}$, its degree-only acceptance-gap property holds, and every coordinatewise degree-at-most-$d$ map satisfies
--
--   $$\operatorname{Ov}(Q(U_s),\operatorname{Ber}(1/3)^{\otimes n})\le\exp(-\delta_d^{\,6}n).$$
--
--   The constants are chosen before all seed lengths, output lengths, and maps. The laws are computed from the sampler; output coordinates can be arbitrarily dependent. No cube-gap, support, entropy, locality, or seed-size condition is assumed. At $n=0$ the bound is $1\le1$. This is the known exponential separation result and its bounded-rank continuation, with the source's exact sixth-power relationship.
--
--   Differences from the source:
--   - encoding: binary vector spaces and Boolean multilinear degree → Fin-indexed ZMod 2 words and evaluation of multilinear MvPolynomial representatives; reason: the same finite binary spaces and the unique Boolean polynomial, including constants and dimension zero
--   - encoding: one positive acceptance-gap witness for each positive rank, with the degree-only witness equal to the rank-one witness → a function δ on natural ranks, constrained only at positive ranks, with the degree-only clause using δ 1; reason: simultaneous choice records the source witness family and changes no instance
--   - encoding: c_d = δ_d^6 and c_d,r = δ_d,r^6, with gap witnesses from Theorem 1 and δ at most one third in the proof → existence of normalized positive acceptance-gap witnesses jointly with unconditional overlap bounds using their sixth powers; reason: makes the unspecified source witness choice self-contained; no gap assumption is added to the goal, and constant-zero functions already force the gap upper bound
-- source:
--   Yan Zhong, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Theorem 4 Eq. (16), printed p. 11 / PDF p. 13, and §3.2 bounded degree-d rank continuation, printed p. 12 / PDF p. 14

import Definitions.Def_PolynomialSampling137_OneThird_FiniteProbability
import Definitions.Def_PolynomialSampling137_OneThird_BooleanSources

namespace PolynomialSampling137.OneThird

/-- Zhong, Theorem 4 and the bounded degree-d rank continuation.
Gap witnesses are chosen before every seed length, output length, and map.
The degree-only clause uses exactly the same rank-one gap witness. -/
theorem one_third_product_separation (d : ℕ) (hd : 1 ≤ d) :
    ∃ δ : ℕ → ℝ,
      (∀ r : ℕ, 1 ≤ r →
        0 < δ r ∧ δ r ≤ 1 / 3 ∧ RankGap d r (1 / 3) (δ r) ∧
        ∀ (s n : ℕ) (Q : Word s → Word n),
          (∀ i, RankLE d r (fun x => Q x i)) →
          overlap (samplerMass Q) (bernoulliProductMass (1 / 3) n) ≤
            Real.exp (-((δ r) ^ 6 * (n : ℝ)))) ∧
      DegreeGap d (1 / 3) (δ 1) ∧
      (∀ (s n : ℕ) (Q : Word s → Word n),
        (∀ i, DegreeLE d (fun x => Q x i)) →
        overlap (samplerMass Q) (bernoulliProductMass (1 / 3) n) ≤
          Real.exp (-((δ 1) ^ 6 * (n : ℝ)))) := by sorry

end PolynomialSampling137.OneThird
