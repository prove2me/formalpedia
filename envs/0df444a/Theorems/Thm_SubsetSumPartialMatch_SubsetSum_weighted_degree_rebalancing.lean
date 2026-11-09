-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_weighted_degree_rebalancing
-- name    : SubsetSumPartialMatch.SubsetSum.weighted_degree_rebalancing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:10.09812+00:00
-- url     : https://prove2.me/theorems/ddf19292-8ce0-468d-abd1-cd2ea45a60d9
-- title:
--   Corollary 3.5 — weighted-degree rebalancing
-- statement:
--   Let $C^{(1)},\dots,C^{(m)}$ be colored EXACT$_\mathbb Z$ circuits computing the same nonzero matrix $M$, among which there are a single-colored circuit with right degree $1$ and a single-colored circuit with left degree $1$, and put $\rho(t)=\min_i\rho_{C^{(i)}}(t)$. Then for every $d\ge0$ and every $\lambda>0$ there is an EXACT$_\mathbb Z$ circuit $E_{d,\lambda}$ computing $M^{\otimes d}$ with
--   $$\deg_L(E_{d,\lambda})+\lambda\deg_R(E_{d,\lambda})\le2^{o(d)}\max_{0\le t\le1}\rho(t)^d\lambda^{1-t},$$
--   where the $o(d)$ term depends on $C^{(1)},\dots,C^{(m)}$ but not on $\lambda$.
--
--   This turns Lemma 3.4 into a statement about circuits.
--
--   Differences from the source:
--   - encoding: $2^{o(d)}$, independent of $\lambda$ → one function $g$ with $g(d)=o(d)$, chosen before $d$ and $\lambda$; reason: this is the quantifier order of the source
--   - encoding: $\max_{0\le\tau\le1}$ → some $t\in[0,1]$ satisfies the bound; reason: the maximum is attained, so the two forms are equivalent
--   - encoding: each circuit has its own color set → one color type $Z$ for all $m$ circuits; reason: colors are labels; finitely many color sets embed in their disjoint union
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 21, Corollary 3.5

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit

namespace SubsetSumPartialMatch.SubsetSum

/-- Corollary 3.5. Let `C^(1), …, C^(m)` be colored EXACT_Z circuits computing one nonzero matrix
`M`, among them a single-colored circuit with right degree `1` and a single-colored circuit with
left degree `1`. Then for all `d ≥ 0` and `λ > 0` there is an EXACT_Z circuit `E` for `M^{⊗d}` with
`deg_L(E) + λ deg_R(E) ≤ 2^{o(d)} max_{0≤t≤1} ρ(t)^d λ^{1-t}`, `ρ = min_i ρ_{C^(i)}`, where the
`o(d)` does not depend on `λ`. The maximum is written as: some `t ∈ [0,1]` satisfies the bound. -/
theorem weighted_degree_rebalancing {I J Z : Type} [Fintype I] [Fintype J] {m : ℕ}
    (C : Fin m → ColoredCircuit I J Z) (M : Matrix I J ℤ) (hM : M ≠ 0)
    (hC : ∀ i, (C i).toLinCircuit.Computes M)
    (hR : ∃ i, (C i).SingleColored ∧ (C i).toLinCircuit.degR = 1)
    (hL : ∃ i, (C i).SingleColored ∧ (C i).toLinCircuit.degL = 1) :
    ∃ g : ℕ → ℝ, Asymptotics.IsLittleO Filter.atTop g (fun d : ℕ => (d : ℝ)) ∧
      ∀ (d : ℕ) (lam : ℝ), 0 < lam →
        ∃ E : LinCircuit (Fin d → I) (Fin d → J), E.Computes (tensorPow M d) ∧
          ∃ t ∈ Set.Icc (0 : ℝ) 1,
            (E.degL : ℝ) + lam * (E.degR : ℝ) ≤
              (2 : ℝ) ^ g d * (⨅ i, (C i).volume t) ^ d * lam ^ (1 - t) := by sorry

end SubsetSumPartialMatch.SubsetSum
