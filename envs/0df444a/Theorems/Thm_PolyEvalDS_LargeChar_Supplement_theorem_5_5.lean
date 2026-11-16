-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_Supplement_theorem_5_5
-- name    : PolyEvalDS.LargeChar.Supplement.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:58:32.5343+00:00
-- url     : https://prove2.me/theorems/96aebf23-0750-4e72-a3e5-fed1c26d03f7
-- title:
--   Theorem 5.5 ([Web25]) — $0/1$ power sums of $b$ take at least $\min\{2^{\gamma/(4\ln\ln\gamma)},2^{\sqrt{2d/(\ln3\ln(3d)^3)}}\}$ values in $\mathbb F_p$
-- statement:
--   Let $p$ be a prime and $d\ge1$ an integer with
--
--   $$
--   (d+1)^{3d/2}<p .
--   $$
--
--   Let $\gamma\ge 7$ be a real number and let $b\in\mathbb F_p^*$ be an element that is not a root of unity of order at most $\gamma$: $b^k\neq1$ for every integer $1\le k\le\gamma$ (its multiplicative order exceeds $\gamma$). Then the number of distinct elements of $\mathbb F_p$ of the form $\sum_{i=0}^{d} a_i b^i$ with $a_0,\dots,a_d\in\{0,1\}$ satisfies
--
--   $$
--   \left|\Big\{\sum_{i=0}^{d}a_ib^i \;\Big|\; a_i\in\{0,1\}\Big\}\right|\;\ge\;\min\Big\{2^{\frac{\gamma}{4\ln\ln\gamma}},\;2^{\sqrt{\frac{2d}{\ln 3\,\ln(3d)^3}}}\Big\} ,
--   $$
--
--   where $\ln$ is the natural logarithm and $\ln(3d)^3=(\ln(3d))^3$.
--
--   The theorem is credited to [Web25] and proved in full in the paper (pp. 12–13). It is the counting lower bound behind Proposition 5.2, the lower bound for separable curve datastructures; it is not used in the proof of the mission's goal, Theorem 1.2.
--
--   **Formalization Note** The set of sums is the image of the powerset of $\{0,\dots,d\}$ under $S\mapsto\sum_{i\in S}b^i$, computed in `ZMod p`, and its cardinality is compared as a real number with the minimum of the two real powers of $2$.
--
--   Differences from the source:
--   - encoding: b ∈ F_p, p a prime → p : ℕ with hp : p.Prime and b : ZMod p; reason: ZMod p is the field F_p for p prime
--   - encoding: d, the degree bound of §5, a positive integer → d : ℕ with hd : 1 ≤ d; reason: the standing assumption of §5 (Prop. 5.2: n, d positive integers), and ln(3d) in the bound is undefined at d = 0; the proof treats d = 1 as its smallest case
--   - encoding: (d+1)^{3d/2} → ((d:ℝ)+1) ^ ((3*(d:ℝ))/2), a real power; reason: 3d/2 is not an integer for odd d; the real power is the printed value
--   - encoding: b ∈ F_p^* is not a root of unity of order ≤ γ → b ≠ 0 and ∀ k : ℕ, 1 ≤ k → (k:ℝ) ≤ γ → b ^ k ≠ 1; reason: every nonzero b ∈ F_p is a root of unity; the hypothesis says its multiplicative order exceeds γ, i.e. b^k ≠ 1 for every integer 1 ≤ k ≤ γ
--   - encoding: γ ≥ 7 → γ : ℝ with 7 ≤ γ; reason: γ is a real parameter in the source (Prop. 5.2 applies it with a square root); no integrality is imposed
--   - encoding: |{∑_{i=0}^d a_i b^i : a_i ∈ {0,1}}| → the cardinality of the image of the powerset of {0,…,d} under s ↦ ∑_{i∈s} b^i, as a Finset of ZMod p; reason: a 0/1 vector (a_0,…,a_d) is the indicator of the subset {i : a_i = 1}; the image counts distinct values in F_p, not choices
--   - encoding: ln, 2^x → Real.log and the real power (2:ℝ) ^ x; reason: natural logarithm and base-2 real exponentiation as printed; all arguments of ln are > 1 under 7 ≤ γ and 1 ≤ d, so no junk value occurs
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Theorem 5.5 ([Web25]), p. 12; proof pp. 12–13

import Mathlib

namespace PolyEvalDS.LargeChar.Supplement

/-- Theorem 5.5 ([Web25]), p. 12, proved on pp. 12–13 (Okada, Player, Pohmann, STOC 2027
submission #463, October 2026). Let `p` be a prime and `d` a positive integer with
`(d + 1)^(3d/2) < p`, let `γ ≥ 7`, and let `b ∈ F_p^*` be no root of unity of order `≤ γ`
(`b ^ k ≠ 1` for every integer `1 ≤ k ≤ γ`). Then the number of distinct values in `F_p` of
`∑_{i=0}^{d} a_i b^i` with `a_i ∈ {0, 1}` is at least
`min {2^(γ / (4 ln ln γ)), 2^√(2d / (ln 3 · ln(3d)^3))}`.
A choice `a ∈ {0,1}^{d+1}` is the subset `{i | a_i = 1}` of `{0, …, d}`; `ln` is `Real.log`. -/
theorem theorem_5_5 (p d : ℕ) (hp : p.Prime) (hd : 1 ≤ d) (γ : ℝ) (hγ : 7 ≤ γ)
    (hpd : ((d : ℝ) + 1) ^ ((3 * (d : ℝ)) / 2) < (p : ℝ))
    (b : ZMod p) (hb0 : b ≠ 0)
    (hb_ord : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ γ → b ^ k ≠ 1) :
    min ((2 : ℝ) ^ (γ / (4 * Real.log (Real.log γ))))
        ((2 : ℝ) ^ Real.sqrt (2 * (d : ℝ) / (Real.log 3 * Real.log (3 * (d : ℝ)) ^ 3)))
      ≤ ((((Finset.range (d + 1)).powerset.image
            (fun s : Finset ℕ => ∑ i ∈ s, b ^ i)).card : ℕ) : ℝ) := by sorry

end PolyEvalDS.LargeChar.Supplement
