-- Prove2me | Theorems.Thm_PolyVoting_conditional_law_given_total
-- name    : PolyVoting.conditional_law_given_total
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:21.657789+00:00
-- url     : https://prove2.me/theorems/00eb05f7-84ea-4d72-ac4b-efa293578004
-- title:
--   p.11 — given $N_t=s$, the stakes are the Pólya urn after $s-N$ draws
-- statement:
--   Let $(\boldsymbol n_t)$ be the Poly($\alpha$) stake process and $(\boldsymbol n^\dagger_j)$ the Pólya urn with the same initial stakes. For all $t$ and $s$ with $\mathbb P(N_t=s)>0$, the conditional law of $\boldsymbol n_t$ given $N_t=s$ is the law of $\boldsymbol n^\dagger_{s-N}$:
--   $$\mathcal L(\boldsymbol n_t\mid N_t=s)=\mathcal L(\boldsymbol n^\dagger_{s-N}).$$
--
--   Applied to the shares, this gives the equality $d_W((\pi_{k,t}\mid N_t=s),Z)=d_W(\pi^\dagger_{k,s-N},Z)$ of the proof of (2.16).
--
--   Differences from the source:
--   - encoding: the Poly(α) rule described by (2.3)–(2.6), K ∈ ℕ₊ bidders, stakes n_{k,t} → `Model μ K α n₀`: the joint conditional one-step law, stakes in Fin K → ℕ, real α ≥ 0 with Real.rpow, and 1 ≤ N; reason: the conditional one-step law and n₀ determine the law of the chain; 1 ≤ N only keeps N_t^{−α} defined
--   - encoding: the Pólya urn with K colours and initial composition n_{k,0} → a `Model` with α = 0 and the same n₀, the Poly(0) instance of the same structure; reason: p.5 identifies α = 0 with the Pólya urn, and at α = 0 the step law is "colour k is drawn with probability n_{k,t}/N_t and one ball of colour k is added"
--   - generalization: d_W((π_{k,t} | N_t = s), Z) = d_W(π†_{k,s−N}, Z) for each k → equality of the conditional law of the stake vector and the law of the urn after s − N draws; reason: the shares are a function of the stake vector, so the page's equality for every k and Z follows
--   - encoding: conditioning on N_t = s, s ≥ λ t^{1/(1+α)} → ProbabilityTheory.cond, for every s with P(N_t = s) ≠ 0; natural subtraction s − N; reason: that hypothesis forces s ≥ N, so the subtraction is exact
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, proof of Theorem 6 (i), p.11, the step d_W((π_{k,t}|N_t = s), Z) = d_W(π†_{k,s−N}, Z)

import Mathlib
import Definitions.Def_PolyVoting_Model

open MeasureTheory ProbabilityTheory

namespace PolyVoting

/-- **The conditional law given `N_t = s`** (Tang & Yao, *Polynomial Voting Rules*,
arXiv:2206.10105v5, p.11, the step `d_W((π_{k,t} | N_t = s), Z) = d_W(π†_{k,s-N}, Z)`): given
`N_t = s`, the stake vector `n_t` has the law of the Pólya urn after `s - N` draws.

**Formalization Note.** This is the statement for stake vectors. The shares are a function of
the stake vector, so the page's equality of Wasserstein distances for each `k` follows from it.
`s - N` is natural subtraction, which is exact here: `μ (N_t = s) ≠ 0` forces `s ≥ N`. -/
theorem conditional_law_given_total {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {K : ℕ} {α : ℝ} {n₀ : Fin K → ℕ} (M : Model μ K α n₀) (U : Model μ' K 0 n₀)
    (t s : ℕ) (hs : μ (M.total t ⁻¹' {s}) ≠ 0) :
    (ProbabilityTheory.cond μ (M.total t ⁻¹' {s})).map (M.n t) =
      μ'.map (U.n (s - ∑ k, n₀ k)) := by sorry

end PolyVoting
