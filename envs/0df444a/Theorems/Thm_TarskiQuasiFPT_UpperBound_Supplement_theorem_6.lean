-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_Supplement_theorem_6
-- name    : TarskiQuasiFPT.UpperBound.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:32:25.749201+00:00
-- url     : https://prove2.me/theorems/679deb36-18c2-4336-8d8a-66b6ef22909b
-- title:
--   Theorem 6 — level-$\ell$ hard distribution on $[m^\ell]^{2(4^\ell-1)/3}$: depth $q_{\ell,m}$ succeeds w.p. at most $3m^{-c_0-1/(8\ell)}$
-- statement:
--   There is an absolute constant $c_0\in(0,1/3)$ with the following property. Let $m\ge200$ and $\ell\ge1$ be integers, and put
--   $$n_{\ell,m}=m^\ell,\qquad k_\ell=\frac{2(4^\ell-1)}3 .$$
--   Then there is a distribution $\mathcal F_{\ell,m}$ of monotone functions $F:[n_{\ell,m}]^{k_\ell}\to[n_{\ell,m}]^{k_\ell}$ such that:
--
--   1. every $F\in\operatorname{supp}(\mathcal F_{\ell,m})$ has a unique fixed point;
--   2. for $F\sim\mathcal F_{\ell,m}$, every deterministic decision tree of depth at most
--   $$q_{\ell,m}=c_0\Big(\frac{\log m}{512\,\ell^3}\Big)^{\ell+1}$$
--   finds the fixed point of $F$ with probability at most $\varepsilon_{\ell,m}=3m^{-c_0-\frac1{8\ell}}$.
--
--   The theorem gives hard input distributions for every level $\ell$, and Theorem 3 follows from it by padding and Yao's minimax principle. It is a companion result to the mission's goal (the upper bound, Theorem 2) and is not used in the goal's proof.
--
--   **Formalization Note** $c_0$ is chosen before $m$ and $\ell$ and is uniform over all of them. $k_\ell$ is computed in $\mathbb N$, where $3$ divides $4^\ell-1$. $\log$ is base two, and $m^{-c_0-1/(8\ell)}$ is a real power.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, points of [n]^k ordered coordinatewise → Point n k = Fin k → Fin n (0-based values) with the pointwise order; reason: shift by one; same order, same instances
--   - encoding: a distribution of functions → PMF over functions; reason: the function spaces are finite, so every distribution is a PMF
--   - encoding: deterministic decision tree of depth at most q → DepthLE T q: T.queries g ≤ q for every oracle g (q real); reason: depth is the longest root-to-leaf path; the real bound is the paper's real expression
--   - reading: the tree "finds the fixed point" of F → the output T.eval F is a fixed point of F; reason: §3 uses "finds" for the output; for a lower bound this is the stronger of the two readings (a tree that queried the fixed point can output it at no extra depth)
--   - encoding: log (base two, footnote 1) → Real.logb 2; reason: the paper's convention
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, Theorem 6, PDF p. 15 (printed p. 14); restated PDF p. 22 (printed p. 21); proof PDF p. 25 (printed p. 24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_Supplement_LowerBound

open QAlgorithms
set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound.Supplement

/-- Theorem 6, PDF p. 15 (restated p. 22). There is an absolute constant `c0 ∈ (0, 1/3)` such
that for all integers `m ≥ 200` and `ℓ ≥ 1`, with `n_{ℓ,m} = m^ℓ` and
`k_ℓ = 2(4^ℓ − 1)/3`, there is a distribution `𝓕_{ℓ,m}` of monotone
`F : [n_{ℓ,m}]^{k_ℓ} → [n_{ℓ,m}]^{k_ℓ}`, each with a unique fixed point, such that every
deterministic decision tree of depth at most `q_{ℓ,m} = c0 (log₂ m / (512 ℓ^3))^{ℓ+1}` finds the
fixed point of `F ∼ 𝓕_{ℓ,m}` with probability at most `ε_{ℓ,m} = 3 m^{−c0 − 1/(8ℓ)}`. -/
theorem theorem_6 :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 < 1 / 3 ∧ ∀ m ℓ : ℕ, 200 ≤ m → 1 ≤ ℓ →
      ∃ D : PMF (Point (m ^ ℓ) (2 * (4 ^ ℓ - 1) / 3) → Point (m ^ ℓ) (2 * (4 ^ ℓ - 1) / 3)),
        (∀ F ∈ D.support, Monotone F ∧ HasUniqueFixedPoint F) ∧
        ∀ T : DecisionTree (Point (m ^ ℓ) (2 * (4 ^ ℓ - 1) / 3))
            (Point (m ^ ℓ) (2 * (4 ^ ℓ - 1) / 3)) (Point (m ^ ℓ) (2 * (4 ^ ℓ - 1) / 3)),
          DepthLE T (c0 * (Real.logb 2 m / (512 * (ℓ : ℝ) ^ 3)) ^ (ℓ + 1)) →
            succProb D T ≤ 3 * (m : ℝ) ^ (-c0 - 1 / (8 * (ℓ : ℝ))) := by sorry

end TarskiQuasiFPT.UpperBound.Supplement
