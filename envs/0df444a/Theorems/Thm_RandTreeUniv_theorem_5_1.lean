-- Prove2me | Theorems.Thm_RandTreeUniv_theorem_5_1
-- name    : RandTreeUniv.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:14.16778+00:00
-- url     : https://prove2.me/theorems/69422b7a-4c7a-478b-93e5-4ac0de1d03e7
-- title:
--   Theorem 5.1 — $G(n,C(\ln n)^\psi/n)$ is whp $\mathcal T_1^*$-universal
-- statement:
--   Let $K$ be a large enough constant, $\psi=\psi(n)\in[1,\ln n/(4\ln\ln n)]$ and $\alpha=n\psi\ln\ln n/(K^3\ln n)$, and let $\mathcal T_1^*$ be the family of graphs on $n$ vertices with $\alpha$ vertex-disjoint bare paths of length $n/(K^2\alpha)$ whose removal leaves a forest of maximum degree at most $\Delta$. There is a constant $C>0$ such that, for every $\Delta\ge2$, with high probability
--
--   $$
--   G\big(n,C(\ln n)^\psi/n\big)\ \text{is}\ \mathcal T_1^*\text{-universal}.
--   $$
--
--   Since $\mathcal T_1\subseteq\mathcal T_1^*$ (for $\psi=1$), this gives the $\mathcal T_1$ part of Theorem 1; it also gives the cycle-factor result Theorem 4.
--
--   Differences from the source:
--   - reading: K is a large enough constant; there is C > 0 → ∃ K₀, ∀ K ≥ K₀, ∃ C > 0 (C depends on K, not on ∆ or ψ); reason: standard reading of 'large enough'; C is chosen after K (D = D(K), p.25)
--   - reading: α paths of length n/(K²α) → ⌈α⌉ paths of length ⌈n/(K²α)⌉; reason: the paper ignores rounding (§2.1); with this reading T₁ ⊆ T₁* holds
--   - reading: for a function ψ(n), whp → uniform over the value ψ at each n (for every ε > 0 there is N …); reason: equivalent to the statement for every function ψ
--   - encoding: vertex set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabelling; same graphs up to isomorphism
--   - encoding: G(n,p) with p = p(n) a probability → published erProb n p, which clamps p to [0,1]; reason: the clamp is the identity on [0,1], and the edge probabilities used lie in [0,1] for all large n
--   - encoding: isomorphic copy as a subgraph → SimpleGraph.IsContained (injective edge-preserving map, not necessarily induced); reason: same notion
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §5, Theorem 5.1, p.25 (PDF 26)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_RandTreeUniv_InT1Star
import Definitions.Def_RandTreeUniv_IsUniversal

set_option autoImplicit false

open scoped Classical
open LPCommunity.SBMRecovery

namespace RandTreeUniv

/-- **Theorem 5.1** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.25 (PDF 26)). There is a constant `C > 0` such that, for every
`∆ ≥ 2`, whp `G(n, C(ln n)^ψ/n)` is `T∗₁`-universal. Here `K` is "a large enough constant",
`ψ = ψ(n) ∈ [1, ln n/(4 ln ln n)]` and `T∗₁` is the family of all graphs on `n` vertices with
`α = nψ ln ln n/(K³ ln n)` vertex-disjoint bare paths of length `n/(K²α)` whose removal leaves a
forest of maximum degree at most `∆`.

**Formalization Note** Quantifiers: there is `K₀` such that for every `K ≥ K₀` there is `C > 0`
(before `∆` and `ψ`) such that for every `∆ ≥ 2` and `ε > 0` there is `N` with: for all `n ≥ N`
and all `ψ ∈ [1, ln n/(4 ln ln n)]`, the probability is at least `1 − ε` (uniformity over the
value of `ψ` at each `n` is equivalent to "for every function `ψ`"). `T∗₁` is `InT1Star` (with
`⌈α⌉` paths of length `⌈n/(K²α)⌉`). `G(n, p)` is the published `erProb`. -/
theorem theorem_5_1 :
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℕ, 2 ≤ Δ →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ ψ : ℝ, 1 ≤ ψ → ψ ≤ Real.log n / (4 * Real.log (Real.log n)) →
          1 - ε ≤ erProb n (C * Real.log n ^ ψ / n) (fun G => IsUniversal G (InT1Star n K ψ Δ)) := by sorry

end RandTreeUniv
