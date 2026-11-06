-- Prove2me | Theorems.Thm_SpinGirth5_proposition_36_tail
-- name    : SpinGirth5.proposition_36_tail
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:58.326166+00:00
-- url     : https://prove2.me/theorems/4afbf0bc-cc96-4f44-aac7-e7c92fdffd3f
-- title:
--   Proposition 36 — $\|P_vh(1-L)\|^2\le O_\alpha(\log(2d)/\Delta^2)\|h\|^2$ on $K_0$
-- statement:
--   For every $\alpha\ge1$ there is $C>0$ depending only on $\alpha$ such that the following holds. Let $\nu$ be the star law (16) with leaf laws $p_1,\dots,p_d$. If $1\le d\le\Delta$, Condition 26 holds and $\Delta\ge2\alpha$, then every $h\in K_0$ satisfies, in $L^2(\nu)$,
--   $$\|P_vh\,(1-L)\|^2\le C\,\frac{\log(2d)}{\Delta^2}\,\|h\|^2,$$
--   with $L=L_\rho$ the likelihood ratio and $\log$ the natural logarithm. It bounds the error from replacing the leaf marginal of $\nu$ by the product law $\rho$.
--
--   Differences from the source:
--   - generalization: ν = µ^τ_{G,N[v]}, p_i = µ^τ_{G−v,i} built from a graph (13) → any multi-spin system (A, λ), any distributions p_1, …, p_d on [q], ν the star law (16) with positive normalizer; reason: the §5 proofs use only (16) and Condition 26; (13) is an instance by p.21
--   - encoding: O_α(·) → ∃ C > 0 chosen after α and before every other datum; reason: the paper's convention: implicit constants depend on α only (§2.1, p.10)
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Proposition 36, Eq. (30), p.27

import Mathlib
import Definitions.Def_SpinGirth5_starModel

namespace SpinGirth5

/-- **Proposition 36**. For every `α ≥ 1` there is `C > 0` (depending on `α` only) such that, for
the star law `ν` of (16) with leaf laws `p_1, …, p_d`, if `1 ≤ d ≤ Δ`, Condition 26 holds and
`Δ ≥ 2α`, then every `h ∈ K₀` satisfies
`‖P_v h · (1 − L)‖² ≤ C · log(2d)/Δ² · ‖h‖²` in `L²(ν)`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Proposition 36, Eq. (30), p.27.

**Formalization Note** `O_α(log(2d)/Δ²)` is `C · log(2d)/Δ²` with `C` chosen after `α` and before
every other datum; `log` is the natural logarithm. -/
theorem proposition_36_tail (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (q d Δ : ℕ) (S : Interaction q) (p : Fin d → Fin q → ℝ),
      (∀ i, MarkovMixing.IsDist (p i)) → 0 < ∑ x, starWeight S p x → 1 ≤ d → d ≤ Δ →
      Condition26 S p (centerMarginal (starDist S p)) α ε Δ → 2 * α ≤ Δ →
      ∀ h : (Option (Fin d) → Fin q) → ℝ, K0 (starDist S p) h →
        MarkovMixing.innerPi (starDist S p)
            (fun x => heatBath (starDist S p) none h x * (1 - likelihoodRatio S p (leafCfg x)))
            (fun x => heatBath (starDist S p) none h x * (1 - likelihoodRatio S p (leafCfg x))) ≤
          C * Real.log (2 * d) / (Δ : ℝ) ^ 2 * MarkovMixing.innerPi (starDist S p) h h := by sorry

end SpinGirth5
