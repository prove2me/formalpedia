-- Prove2me | Theorems.Thm_SpinGirth5_proposition_32_concentration
-- name    : SpinGirth5.proposition_32_concentration
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:51.613316+00:00
-- url     : https://prove2.me/theorems/77a2f9d1-3e02-4a07-a234-224fa22dde55
-- title:
--   Proposition 32 — concentration of the likelihood ratio $L_\rho$ under every centre colour
-- statement:
--   For every $\alpha\ge1$ there are constants $C_\alpha,c_\alpha>0$ depending only on $\alpha$ such that the following holds. Let $\nu$ be the star law (16) with leaf laws $p_1,\dots,p_d$, $\rho=\bigotimes_{i=1}^dp_i$ and $L=L_\rho$. Suppose $1\le d\le\Delta$, the $\alpha$-marginal bound of Condition 26 holds and $\Delta\ge2\alpha$. Then for every $t\ge2C_\alpha d/\Delta^2$,
--   $$\sup_{\mathfrak r:\ \nu(v\mathfrak r)>0}\Pr_{\nu^{v\mathfrak r}}\big[|L-1|>t\big]\le2\exp\Big(-c_\alpha\frac{\Delta^2}{d}t^2\Big)\le2\exp\big(-c_\alpha\Delta t^2\big),$$
--   where $\nu^{v\mathfrak r}$ is the law of the leaves given centre colour $\mathfrak r$.
--
--   It says that the leaf marginal of $\nu$ is close to the product law $\rho$ uniformly over the centre colour; it is used in the bound (14) on $\|(P_v)_{00}\|$ and in Proposition 36.
--
--   Differences from the source:
--   - generalization: ν = µ^τ_{G,N[v]}, p_i = µ^τ_{G−v,i} built from a graph (13) → any multi-spin system (A, λ), any distributions p_1, …, p_d on [q], ν the star law (16) with positive normalizer; reason: the §5 proofs use only (16) and Condition 26; (13) is an instance by p.21
--   - encoding: constants C_α, c_α → ∃ C_α, c_α > 0 chosen after α and before every other datum; reason: they depend on α only
--   - encoding: sup over 𝔯 with ν(v𝔯) > 0 of Pr_{ν^{v𝔯}}[|L − 1| > t] → for each such 𝔯, ∑_{x : x_v = 𝔯, |L(x_{N(v)}) − 1| > t} ν(x) / ν_v(𝔯) bounded by the right-hand side; reason: a bound on a supremum over a finite set is a bound on each term
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Proposition 32, Eq. (17), p.23

import Mathlib
import Definitions.Def_SpinGirth5_starModel

namespace SpinGirth5

open Finset

/-- **Proposition 32** (concentration of the likelihood ratio). For every `α ≥ 1` there are
constants `C_α, c_α > 0` such that the following holds. Let `ν` be the star law (16) with leaf
laws `p_1, …, p_d`, `ρ = ⊗_i p_i`, and `L = L_ρ = ν_{N(v)}/ρ`. If `1 ≤ d ≤ Δ`, the α-marginal
bound of Condition 26 holds and `Δ ≥ 2α`, then for every `t ≥ 2 C_α d/Δ²`,
`sup_{r : ν(v_r) > 0} Pr_{ν^{v_r}}[|L − 1| > t] ≤ 2 exp(−c_α (Δ²/d) t²) ≤ 2 exp(−c_α Δ t²)`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Proposition 32, Eq. (17), p.23.

**Formalization Note** `C_α, c_α` are chosen after `α` and before every other datum. The law
`ν^{v_r}` of the leaves given centre colour `r` is `ν(· | X_v = r)`, so its probability of
`|L − 1| > t` is `∑_{x : x_v = r, |L(x_{N(v)}) − 1| > t} ν(x) / ν_v(r)`; the supremum over `r`
with `ν_v(r) > 0` is a bound for each such `r`. -/
theorem proposition_32_concentration (α : ℝ) (hα : 1 ≤ α) :
    ∃ Cα cα : ℝ, 0 < Cα ∧ 0 < cα ∧
      ∀ (q d Δ : ℕ) (S : Interaction q) (p : Fin d → Fin q → ℝ),
      (∀ i, MarkovMixing.IsDist (p i)) → 0 < ∑ x, starWeight S p x →
      1 ≤ d → d ≤ Δ → MarginalBound S p (centerMarginal (starDist S p)) α Δ → 2 * α ≤ Δ →
      ∀ t : ℝ, 2 * Cα * d / (Δ : ℝ) ^ 2 ≤ t → ∀ r : Fin q, 0 < centerMarginal (starDist S p) r →
        (∑ x ∈ univ.filter (fun x : Option (Fin d) → Fin q =>
            x none = r ∧ t < |likelihoodRatio S p (leafCfg x) - 1|), starDist S p x) /
            centerMarginal (starDist S p) r ≤
          2 * Real.exp (-cα * ((Δ : ℝ) ^ 2 / d) * t ^ 2) ∧
        2 * Real.exp (-cα * ((Δ : ℝ) ^ 2 / d) * t ^ 2) ≤ 2 * Real.exp (-cα * Δ * t ^ 2) := by sorry

end SpinGirth5
