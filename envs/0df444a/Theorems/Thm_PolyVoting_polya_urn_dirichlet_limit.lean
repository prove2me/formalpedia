-- Prove2me | Theorems.Thm_PolyVoting_polya_urn_dirichlet_limit
-- name    : PolyVoting.polya_urn_dirichlet_limit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:25.849504+00:00
-- url     : https://prove2.me/theorems/37bacb5d-5eab-4750-bf1f-532e44287d15
-- title:
--   p.11 — the limiting shares of a Pólya urn have law $\mathrm{Dir}(n_{1,0},\dots,n_{K,0})$
-- statement:
--   Consider a Pólya urn (the Poly(0) model) with initial composition $(n_{1,0},\dots,n_{K,0})$, every $n_{k,0}\ge1$. The share vector converges almost surely, and its limit has the law
--   $$\mathrm{Dir}(n_{1,0},\dots,n_{K,0}).$$
--
--   This is the classical limit theorem for the Pólya urn, which the paper transfers to every $\alpha$ through Proposition 1.
--
--   Differences from the source:
--   - encoding: the Poly(α) rule described by (2.3)–(2.6), K ∈ ℕ₊ bidders, stakes n_{k,t} → `Model μ K α n₀`: the joint conditional one-step law, stakes in Fin K → ℕ, real α ≥ 0 with Real.rpow, and 1 ≤ N; reason: the conditional one-step law and n₀ determine the law of the chain; 1 ≤ N only keeps N_t^{−α} defined
--   - encoding: the Pólya urn with K colours and initial composition n_{k,0} → a `Model` with α = 0 and the same n₀, the Poly(0) instance of the same structure; reason: p.5 identifies α = 0 with the Pólya urn, and at α = 0 the step law is "colour k is drawn with probability n_{k,t}/N_t and one ball of colour k is added"
--   - encoding: Dir has a density on the simplex in ℝ^K → pushforward under y ↦ (y, 1 − Σy) of the density on the first K − 1 coordinates (point mass at 1 for K = 1); reason: the simplex is a Lebesgue null set of ℝ^K; this is the standard meaning of the density; dirichletMeasure_two in the verification file checks K = 2 against Beta
--   - encoding: the limiting shares of the urn and their law → ∃ measurable πInf: a.s. limit of the share vectors, with law Dir; reason: measurability makes the law well defined
--   - encoding: Dir(n_{1,0}, …, n_{K,0}) → the clause is guarded by every n₀ j ≥ 1; reason: the guard only excludes undefined laws: a zero parameter has no density
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, proof of Theorem 6 (i), p.11, "the Pólya urn, which is Dir(n1,0, . . . , nK,0)"

import Mathlib
import Definitions.Def_PolyVoting_Model
import Definitions.Def_PolyVoting_dirichletMeasure

open MeasureTheory Filter Topology

namespace PolyVoting

/-- **The limiting shares of a Pólya urn are Dirichlet** (Tang & Yao, *Polynomial Voting Rules*,
arXiv:2206.10105v5, p.11): the share vector of a Pólya urn (the `α = 0` model) with every
`n₀ j ≥ 1` converges almost surely to a limit with law `Dir(n₀)`. -/
theorem polya_urn_dirichlet_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℕ} {n₀ : Fin K → ℕ} (U : Model μ K 0 n₀)
    (hn₀ : ∀ j, 1 ≤ n₀ j) :
    ∃ πInf : Ω → Fin K → ℝ, Measurable πInf ∧
      (∀ᵐ ω ∂μ, Tendsto (fun t k => U.share k t ω) atTop (𝓝 (πInf ω))) ∧
      μ.map πInf = dirichletMeasure fun j => (n₀ j : ℝ) := by sorry

end PolyVoting
