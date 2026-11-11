-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_lemma_B_1
-- name    : SpanForestStream.Unrestricted.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:31:41.914236+00:00
-- url     : https://prove2.me/theorems/984277f4-9b0d-403c-a256-cb75f4360c47
-- title:
--   Lemma B.1 — (2b+2)-wise independent hashes with O(bA) seed bits, and the tails (B.1)–(B.2) (work bound not stated)
-- statement:
--   Let $N_E=\binom v2$, $A=\lceil\log_2(v+1)\rceil$ and $b\ge 8$ an integer.
--
--   (i) There is an absolute constant $C$ such that, for every $v\ge 2$, a bank has a $(2b+2)$-wise independent map from the $N_E$ edge names to $h=\lceil\log_2(N_E+1)\rceil+8$ bits whose seed has at most $C\,bA$ bits: under a uniform seed, the hash values of any at most $2b+2$ names are independent and uniform on $\{0,1\}^h$.
--
--   (ii) Suppose the level-$j$ sampling indicators of the names are $(2b+2)$-wise independent with rate $p=2^{-j}$. For any fixed finite set of names, its sampled size $X$ has mean $\mu=|S|\,2^{-j}$ and
--   $$\mathbb E|X-\mu|^{2b}\le 4\,(4b\mu+16b^2)^b,\qquad(\text{B.1})$$
--   $$\mu\ge 64b\implies \Pr(X<b)\le 2^{-b},\qquad \mu\le 128b\implies \Pr(X>512b)\le 2^{-b}.\qquad(\text{B.2})$$
--
--   These tails are the per-cut sampling guarantees behind the algorithm's cut recovery (§3).
--
--   Differences from the source:
--   - generalization: the level-j indicators of the bank's hash on the (v choose 2) names, for levels j ≤ h → any law of an indicator family on any index type whose indicators are (2b+2)-wise independent Bernoulli(2^{-j}), for every level j ∈ ℕ; reason: the bank's level indicators form such a family (a name is kept at level j iff j uniform hash bits are zero), so the source's case is an instance
--   - reading: the map has polynomial setup and evaluation work in v + b → not stated; reason: a running-time claim about the implementation, which needs a machine model the mission does not have (running time is stated separately from Theorems 1.1/1.2, §1.2)
--   - encoding: O(bA) seed bits → a uniform seed in {0,1}^n with n ≤ C·b·A for one absolute C; reason: O(·) as an absolute constant
--   - encoding: E|X − μ|^{2b} → the [0,∞]-valued sum Σ_ω P(ω)·|X(ω) − μ|^{2b} with μ = |S|·2^{-j}; reason: the expectation of a nonnegative variable; μ is the mean computed from the rate
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 46 (PDF 49), Lemma B.1, Eqs. (B.1)–(B.2)

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Stream
import Definitions.Def_SpanForestStream_Unrestricted_SpaceFunction
import Definitions.Def_SpanForestStream_Unrestricted_KWiseBernoulli

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Lemma B.1 (explicit hashes and bounded-independence tails), without its running-time clause.
(i) There is an absolute `C` such that for `v ≥ 2` and `b ≥ 8` a bank has a `(2b+2)`-wise independent
uniform map from the `N_E = (v choose 2)` names to `h = ⌈log₂(N_E + 1)⌉ + 8` bits with at most
`C b A` seed bits, `A = ⌈log₂(v+1)⌉`.
(ii) Eqs. (B.1)–(B.2): for `b ≥ 8` and `(2b+2)`-wise independent level-`j` indicators of rate
`p = 2^{-j}`, the sampled size `X` of a fixed set `S` of names, with mean `μ = |S| p`, satisfies
`E|X − μ|^{2b} ≤ 4(4bμ + 16b²)^b`; if `μ ≥ 64b` then `Pr(X < b) ≤ 2^{-b}`; if `μ ≤ 128b` then
`Pr(X > 512b) ≤ 2^{-b}`. -/
theorem lemma_B_1 :
    (∃ C : ℝ, 0 < C ∧ ∀ (v b : ℕ), 2 ≤ v → 8 ≤ b →
      ∃ (n : ℕ) (hash : (Fin n → Bool) → EdgeName v →
          (Fin (⌈Real.logb 2 ((v.choose 2 : ℝ) + 1)⌉₊ + 8) → Bool)),
        (n : ℝ) ≤ C * b * ceilLog v ∧
        ∀ T : Finset (EdgeName v), T.card ≤ 2 * b + 2 →
          ∀ a : EdgeName v → (Fin (⌈Real.logb 2 ((v.choose 2 : ℝ) + 1)⌉₊ + 8) → Bool),
            (PMF.uniformOfFintype (Fin n → Bool)).toOuterMeasure
                {σ | ∀ e ∈ T, hash σ e = a e} =
              ((2 : ℝ≥0∞) ^ (⌈Real.logb 2 ((v.choose 2 : ℝ) + 1)⌉₊ + 8))⁻¹ ^ T.card) ∧
    ∀ (b : ℕ), 8 ≤ b → ∀ {ι : Type} (P : PMF (ι → Bool)) (j : ℕ),
      IsKWiseBernoulli P (2 * b + 2) (ENNReal.ofReal ((1 / 2 : ℝ) ^ j)) →
      ∀ S : Finset ι,
      (∑' ω, P ω * ENNReal.ofReal
          (|(sampledSize S ω : ℝ) - (S.card : ℝ) * (1 / 2 : ℝ) ^ j| ^ (2 * b)) ≤
        ENNReal.ofReal
          (4 * (4 * (b : ℝ) * ((S.card : ℝ) * (1 / 2 : ℝ) ^ j) + 16 * (b : ℝ) ^ 2) ^ b)) ∧
      (64 * (b : ℝ) ≤ (S.card : ℝ) * (1 / 2 : ℝ) ^ j →
        P.toOuterMeasure {ω | sampledSize S ω < b} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ b)) ∧
      ((S.card : ℝ) * (1 / 2 : ℝ) ^ j ≤ 128 * (b : ℝ) →
        P.toOuterMeasure {ω | 512 * b < sampledSize S ω} ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ b)) := by sorry

end SpanForestStream.Unrestricted
