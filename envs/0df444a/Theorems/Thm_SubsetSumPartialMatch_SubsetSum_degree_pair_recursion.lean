-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_degree_pair_recursion
-- name    : SubsetSumPartialMatch.SubsetSum.degree_pair_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:18.204132+00:00
-- url     : https://prove2.me/theorems/9ed42e77-fb05-4d85-898c-bb791ce9d2ce
-- title:
--   Lemma 3.4 — degree-pair volume recursion
-- statement:
--   Let $W_1,\dots,W_m$ be degree-pair lists, including a trivial list of each of the two forms, and let $F_d$ be the recursion $F_0(\lambda)=1+\lambda$, $F_d(\lambda)=\min_i\sum_{(a,b)\in W_i}aF_{d-1}(\lambda b/a)$. Then
--   $$F_d(\lambda)\le2^{o(d)}\max_{0\le t\le1}\rho(t)^d\lambda^{1-t},\qquad\rho(t)=\min_{1\le i\le m}\rho_{W_i}(t),$$
--   where the $o(d)$ term depends on $W_1,\dots,W_m$ but not on $\lambda$.
--
--   The lemma controls the weighted degree of the best rebalancing through the volumes alone. The source states it as essentially [AL25, Theorem B.2] and gives no proof of its own.
--
--   Differences from the source:
--   - encoding: $2^{o(d)}$, independent of $\lambda$ → one function $g$ with $g(d)=o(d)$, chosen before $d$ and $\lambda$; reason: this is the quantifier order of the source
--   - encoding: $\max_{0\le\tau\le1}$ → some $t\in[0,1]$ satisfies the bound; reason: the maximum is attained, so the two forms are equivalent
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 20, Lemma 3.4

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_DegreePairs

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 3.4. Let `W_1, …, W_m` be degree-pair lists, including a trivial list of each of the two
forms. Then `F_d(λ) ≤ 2^{o(d)} max_{0≤t≤1} ρ(t)^d λ^{1-t}`, where `ρ = min_i ρ_{W_i}` and the
`o(d)` term does not depend on `λ`. The maximum is written as: some `t ∈ [0,1]` satisfies the
bound. -/
theorem degree_pair_recursion {m : ℕ} (W : Fin m → List (ℝ × ℝ))
    (hW : ∀ i, IsDegreePairList (W i))
    (hL : ∃ i, IsTrivialLeft (W i)) (hR : ∃ i, IsTrivialRight (W i)) :
    ∃ g : ℕ → ℝ, Asymptotics.IsLittleO Filter.atTop g (fun d : ℕ => (d : ℝ)) ∧
      ∀ (d : ℕ) (lam : ℝ), 0 < lam → ∃ t ∈ Set.Icc (0 : ℝ) 1,
        recF W d lam ≤ (2 : ℝ) ^ g d * (⨅ i, listVolume (W i) t) ^ d * lam ^ (1 - t) := by sorry

end SubsetSumPartialMatch.SubsetSum
