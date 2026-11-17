-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_c_23
-- name    : PolyContract.Supplement.theorem_c_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:07:48.276471+00:00
-- url     : https://prove2.me/theorems/8508b6b8-e300-4e9d-818c-ba7acd6204dd
-- title:
--   Theorem C.23 — every level $j\le k-1$ is a comb on $[R_0,\infty)$ with contacts $\Gamma_j$
-- statement:
--   Let $\mu^{\mathrm{in}}\in\mathcal F$ have length $k$, build the levels $0,\dots,k-1$ by the parameter rule, and let $\kappa:=\min(1,\varepsilon_0/\delta)$ with $\delta=1/(3\mu^{\mathrm{in}}_1)$. Then every level $j\le k-1$ satisfies
--
--   1. $L_j(\alpha)-r(\xi^{(j)}(\alpha))\ge\kappa\min(\operatorname{dist}(\alpha,\Gamma_j),\delta)$ for all $\alpha\ge R_0$;
--   2. $r(\xi^{(j)}(\gamma))=L_j(\gamma)$ for every $\gamma\in\Gamma_j$;
--   3. for $j\ge1$, the hypotheses (W1)–(W6) of Lemma C.15 hold at the step $j-1\to j$.
--
--   So the reward of the full-plane best response of each level stays below its line on $[R_0,\infty)$ and touches it exactly on the $2^{j+1}$ points of $\Gamma_j$.
--
--   Differences from the source:
--   - encoding: min(dist(α, Γ_j), δ) → the published combDist (Γ_j is nonempty); reason: the base convention for the comb predicate
--   - encoding: the levels and r(ξ^{(j)}) → one ambient element type; the published full-plane reward of g_j; reason: the full-plane best response exists and is unique (published milestone)
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem C.23, App. C.7, p.70 (PDF p.71)

import Mathlib
import Definitions.Def_PolyContract_IsComb
import Definitions.Def_PolyContract_Supplement_HypC15

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem C.23** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, App. C.7, p.70): let `µ^in ∈ F` have length `k`, build the levels `0, …, k − 1` by the
parameter rule, and let `κ := min(1, ε₀/δ)`. Then every level `j ≤ k − 1` satisfies
(H_j) `L_j(α) − r(ξ^{(j)}(α)) ≥ κ min(dist(α, Γ_j), δ)` for all `α ≥ R₀`, and `r(ξ^{(j)}(γ)) = L_j(γ)`
for every `γ ∈ Γ_j`, and for `j ≥ 1` the hypotheses of Lemma C.15 hold at the step `j − 1 → j`.

**Formalization Note** The length of `µ^in` is called `n` here. `δ = 1/(3µ^in_1)` is the width
`δw µ^in`, and `min(dist(α, Γ_j), δ)` is the published `combDist` (`Γ_j` is nonempty).
`r(ξ^{(j)})` is the reward of the full-plane best response of `g_j`. -/
theorem theorem_c_23 (μin : List ℕ) (hμ : PerturbedPow8 μin) (n : ℕ) (hlen : μin.length = n)
    (j : ℕ) (hj : j + 1 ≤ n) :
    (∀ α : ℝ, R0 ≤ α →
      min 1 (ε0 / δw μin) * combDist (Γlev μin j) (δw μin) α ≤ gap μin j α) ∧
    (∀ γ ∈ Γlev μin j, rewardLev μin j γ = lineLev μin j γ) ∧
    (1 ≤ j → HypC15 μin (j - 1)) := by sorry

end PolyContract.Supplement
