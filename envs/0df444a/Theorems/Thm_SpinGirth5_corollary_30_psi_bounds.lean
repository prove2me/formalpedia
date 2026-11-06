-- Prove2me | Theorems.Thm_SpinGirth5_corollary_30_psi_bounds
-- name    : SpinGirth5.corollary_30_psi_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:40.921014+00:00
-- url     : https://prove2.me/theorems/2591df47-d614-4d43-b883-985217417282
-- title:
--   Corollary 30 — $|\Psi_i(\mathfrak c,\mathfrak d)|=O_\alpha(\Delta^{-1})$ and $\||\Psi_i|\nu_v\|_\infty=O_\alpha(\Delta^{-2})$
-- statement:
--   For every $\alpha\ge1$ there is a constant $C>0$ depending only on $\alpha$ with the following property. Let $\nu$ be the star law (16) of a multi-spin system $(A,\lambda)$ with leaf laws $p_1,\dots,p_d$ (positive normalizer), and let $\nu_v$ be its centre marginal. If Condition 26 holds with $(\alpha,\varepsilon,\Delta)$ and $\Delta\ge2\alpha$, then
--
--   1. $|\Psi_i(\mathfrak c,\mathfrak d)|\le C/\Delta$ for every leaf $i$ and colours $\mathfrak c,\mathfrak d$;
--   2. $\displaystyle\big\||\Psi_i|\,\nu_v\big\|_\infty=\max_{\mathfrak c}\sum_{\mathfrak d}|\Psi_i(\mathfrak c,\mathfrak d)|\,\nu_v(\mathfrak d)\le C/\Delta^2$ for every leaf $i$.
--
--   These bounds control the products $\prod_i(1+\Psi_i)$ that appear in Proposition 32 and Proposition 35.
--
--   Differences from the source:
--   - generalization: ν = µ^τ_{G,N[v]}, p_i = µ^τ_{G−v,i} built from a graph (13) → any multi-spin system (A, λ), any distributions p_1, …, p_d on [q], ν the star law (16) with positive normalizer; reason: the §5 proofs use only (16) and Condition 26; (13) is an instance by p.21
--   - encoding: O_α(·) → ∃ C > 0 chosen after α and before every other datum; reason: the paper's convention: implicit constants depend on α only (§2.1, p.10)
--   - encoding: ‖·‖∞ of |Ψ_i| ν_v → a bound on every entry ∑_𝔡 |Ψ_i(𝔠,𝔡)| ν_v(𝔡); reason: the entries are nonnegative, so the max-norm bound is the bound on each entry
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Corollary 30, p.22 (Condition 26, p.20)

import Mathlib
import Definitions.Def_SpinGirth5_starModel

namespace SpinGirth5

/-- **Corollary 30**. For every `α ≥ 1` there is `C > 0` (depending on `α` only) such that, for
the star law `ν` of (16) with leaf laws `p_1, …, p_d`, under Condition 26 and `Δ ≥ 2α`:
* `|Ψ_i(c, d)| ≤ C/Δ` for every leaf `i` and colours `c, d`;
* `‖ |Ψ_i| ν_v ‖_∞ ≤ C/Δ²` for every leaf `i`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Corollary 30, p.22 (Condition 26, p.20; Ψ_i, p.22).

**Formalization Note** `O_α(·)` is `∃ C > 0` chosen after `α` and before `ε, q, d, Δ, A, λ, p_i`.
`ν_v` is the centre marginal of the normalized star law (normalizer assumed positive), and the
`ℓ^∞` norm of `|Ψ_i| ν_v` is the maximum over `c` of `∑_d |Ψ_i(c, d)| ν_v(d)`. -/
theorem corollary_30_psi_bounds (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (q d Δ : ℕ) (S : Interaction q) (p : Fin d → Fin q → ℝ),
      (∀ i, MarkovMixing.IsDist (p i)) → 0 < ∑ x, starWeight S p x →
      Condition26 S p (centerMarginal (starDist S p)) α ε Δ → 2 * α ≤ Δ →
      (∀ i c e, |Psi S.A (p i) c e| ≤ C / Δ) ∧
      (∀ i c, ∑ e, |Psi S.A (p i) c e| * centerMarginal (starDist S p) e ≤ C / (Δ : ℝ) ^ 2) := by sorry

end SpinGirth5
