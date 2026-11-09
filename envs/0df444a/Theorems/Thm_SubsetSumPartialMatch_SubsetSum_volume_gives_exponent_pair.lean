-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_volume_gives_exponent_pair
-- name    : SubsetSumPartialMatch.SubsetSum.volume_gives_exponent_pair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:20.776192+00:00
-- url     : https://prove2.me/theorems/9868fe7e-c28d-46fc-b6cd-e4d2d6774400
-- title:
--   Lemma 3.6 — colored volume gives exponent pairs
-- statement:
--   Let $V:[0,1]\to\mathbb R_{\ge0}$, and suppose that for every even $k\ge2$ there is a colored EXACT$_\mathbb Z$ circuit $C_k$ computing $P_{k,1/2}$ such that $\rho_{C_k}(t)\le2^{(V(t)+o(1))k}$ uniformly in $t\in[0,1]$. Then every pair $(l,r)\in\mathbb R^2$ with
--   $$t\,l+(1-t)\,r\ge\min\Bigl\{V(t),\,t,\,\frac{1-t}2\Bigr\}\quad\text{for all }t\in[0,1]$$
--   belongs to $K(1/2)$.
--
--   This is the form in which rebalancing is used: a bound on colored volume yields points of $K(1/2)$.
--
--   Differences from the source:
--   - encoding: $o(1)$ uniform in $t$ → one function $\mathrm{err}(k)\to0$, chosen before $k$ and $t$; reason: this is the meaning of a uniform $o(1)$
--   - encoding: $V$ defined on $[0,1]$ → $V:\mathbb R\to\mathbb R$, used and constrained on $[0,1]$ only; reason: values off $[0,1]$ never occur
--   - encoding: each $C_k$ has its own color set → one color type $Z$ for all $k$; reason: colors are labels; the sets embed in their disjoint union
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 22, Lemma 3.6

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 3.6. Let `V : [0,1] → ℝ_{≥0}` and suppose that every even `k ≥ 2` has a colored EXACT_Z
circuit `C_k` for `P_{k,1/2}` with `ρ_{C_k}(t) ≤ 2^{(V(t)+o(1))k}` uniformly in `t ∈ [0,1]`. Then
every `(l, r) ∈ ℝ²` with `t l + (1-t) r ≥ min {V(t), t, (1-t)/2}` for all `t ∈ [0,1]` belongs to
`K(1/2)`. -/
theorem volume_gives_exponent_pair {Z : Type} (V : ℝ → ℝ)
    (hV : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V t)
    (err : ℕ → ℝ) (herr : Filter.Tendsto err Filter.atTop (nhds 0))
    (hC : ∀ k : ℕ, 2 ≤ k → Even k →
      ∃ C : ColoredCircuit (BinStr k) (PMCol k (1 / 2)) Z,
        C.toLinCircuit.Computes (pm k (1 / 2)) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, C.volume t ≤ (2 : ℝ) ^ ((V t + err k) * k))
    (l r : ℝ)
    (hlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, min (V t) (min t ((1 - t) / 2)) ≤ t * l + (1 - t) * r) :
    (l, r) ∈ K (1 / 2) := by sorry

end SubsetSumPartialMatch.SubsetSum
