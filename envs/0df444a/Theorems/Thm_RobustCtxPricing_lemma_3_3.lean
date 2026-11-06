-- Prove2me | Theorems.Thm_RobustCtxPricing_lemma_3_3
-- name    : RobustCtxPricing.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:11.101059+00:00
-- url     : https://prove2.me/theorems/6e0b5594-107b-4c93-a7bb-c9be512baaa4
-- title:
--   Lemma 3.3 — a correct predicting evidence set's interval contains the valuation
-- statement:
--   Let $d\ge1$, $\theta^\star\in\Theta$, and let $\mathcal H=\{(u_1,p_1),\dots,(u_k,p_k)\}$ be a correct evidence set: $|\langle\theta^\star,u_i\rangle-p_i|\le\epsilon$ for every $i$. If coefficients $\lambda\in\mathbb R^k$ satisfy (1) for a context $u$, i.e. $\epsilon\|\lambda\|_1+\|u-\sum_i\lambda_iu_i\|_2\le\frac1{8T}$, then
--   $$
--   \langle\theta^\star,u\rangle\in I(u)=\Big[\hat v(u)-\frac1{8T},\ \hat v(u)+\frac1{8T}\Big],\qquad \hat v(u)=\sum_{i=1}^k\lambda_ip_i .
--   $$
--   A correct evidence set that predicts $u$ therefore pins down the valuation in direction $u$ to within $\frac1{8T}$.
--
--   Differences from the source:
--   - generalization: ϵ = T⁻³ (set by the algorithm) → any real ϵ and any T ∈ ℕ; reason: the statement holds for every ϵ and T and specializes to ϵ = T⁻³
--   - generalization: "the coefficients which satisfy Equation (1)" (the solution of the minimization) → every λ achieving (1); reason: specializes to the minimizer used in (2)
--   - encoding: evidence set 𝓗_j → a finite list of samples (u_i, p_i); reason: Lean convention; same instances
--   - reading: 𝓑_d(0,1), "the d-dimensional Euclidean ball" → the closed unit ball; reason: the analysis uses ‖u_t‖₂ ≤ 1 and ‖θ⋆‖₂ ≤ 1 (pp.18, 21); the closed ball contains the open one and differs from it by a null set
--   - encoding: the dimension d ∈ ℕ of ℝ^d → a natural number d with 1 ≤ d; reason: the context dimension of the model; d = 0 has no directions and is not an instance of it
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Lemma 3.3, p.15

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence

namespace RobustCtxPricing

/-- **Lemma 3.3.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual
Pricing*, arXiv:2607.11210, §3.2.1, p.15: "Fix a correct evidence set `𝓗_j`. If `𝓗_j` satisfies
Equation (1) for a context `u`, then the interval `I_j(u)` defined in Equation (2) contains
`⟨θ⋆, u⟩`."

For `θ⋆ ∈ Θ`, an evidence set `H` all of whose samples are correct (`|⟨θ⋆, u_i⟩ − p_i| ≤ ϵ`), a
context `u` and coefficients `λ` satisfying (1), the value `⟨θ⋆, u⟩` lies in
`I(u) = [v̂(u) − 1/(8T), v̂(u) + 1/(8T)]` with `v̂(u) = ∑ λ_i p_i`.

**Formalization Note.** Stated for every `ϵ` and `T` (the paper's `ϵ = T⁻³` is a special case),
every finite evidence set and every `λ` achieving (1) (the interval (2) is built from "the solution
to the inequality", p.14). -/
theorem lemma_3_3 (d : ℕ) (hd : 1 ≤ d) (ϵ : ℝ) (T : ℕ) (θ : EuclideanSpace ℝ (Fin d))
    (hθ : θ ∈ Theta d) (H : List (EuclideanSpace ℝ (Fin d) × ℝ)) (hH : SetCorrect ϵ θ H)
    (u : EuclideanSpace ℝ (Fin d)) (lam : Fin H.length → ℝ) (hlam : PredictsWith ϵ T H u lam) :
    inner ℝ θ u ∈ Set.Icc (estimate H lam - 1 / (8 * (T : ℝ))) (estimate H lam + 1 / (8 * (T : ℝ))) := by sorry

end RobustCtxPricing
