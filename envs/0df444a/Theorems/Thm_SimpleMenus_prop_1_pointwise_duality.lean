-- Prove2me | Theorems.Thm_SimpleMenus_prop_1_pointwise_duality
-- name    : SimpleMenus.prop_1_pointwise_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:07.009194+00:00
-- url     : https://prove2.me/theorems/55934005-167f-40f5-a9e5-ca7254b7a631
-- title:
--   Proof of Proposition 1, p.ec7 (corrected: constraint qualification) — per-price strong duality for the homogenized problem
-- statement:
--   Assume Assumption 1 and the constraint qualification (every $\phi_k$ is a step function, or some $F_0\in\mathcal F$ has $\int\phi_k\,dF_0>0$ for every non-step $\phi_k$). Let $\pi$ be an $n$-level mechanism with price levels in $[0,\bar v]$ and expected payment $t$, and let $p\in[0,\bar v]$. Then the homogenized problem and its dual have the same value:
--
--   $$\inf\Bigl\{\int t\,dH_p:\ H_p\ge0,\ \int_{[p,\bar v]}dH_p=1,\ \int\phi_k\,dH_p\ge0\Bigr\}=\sup\Bigl\{\lambda_0:\ \lambda_0\in\mathbb R,\ \lambda\in\mathbb R^K_+,\ \sum_k\phi_k(w)\lambda_k\le t(w)\ (w\in[0,p)),\ \lambda_0+\sum_k\phi_k(w)\lambda_k\le t(w)\ (w\in[p,\bar v])\Bigr\}.$$
--
--   The paper justifies this step by Sion's theorem; neither feasible set is compact, and without the constraint qualification the step fails.
--
--   **Formalization Note** Values are extended reals.
--
--   Differences from the source:
--   - correction: no condition beyond Assumption 1 → ConstraintQualification: every ϕ_k is a step function, or some F₀ ∈ 𝓕 has ∫ ϕ_k dF₀ > 0 for every non-step ϕ_k; reason: the printed statement is false: K = 1, 0 < c < v̄, ϕ(w) = min(w − c, 0), V = {c}, x = 1 satisfies Assumption 1 with CR = c/v̄ but (3) and (4) have value 0, and at p ∈ (0, c] the homogenized primal is c while its dual is 0
--   - reading: Assumption 1 (bounded, piecewise continuous with finite segments, nondecreasing within each segment) → Assumption1: bounded on [0,v̄], and a finite P ⊆ [0,v̄] per k with ϕ_k continuous and monotone on every open piece cut by P; reason: broadest reading of "finite segments"; values at the breakpoints are free
--   - generalization: k = 1, …, K → ϕ : Fin K → ℝ → ℝ with K = 0 allowed; reason: K = 0 is the set of all laws on [0,v̄]; every K ≥ 1 is included
--   - encoding: dH_p ≥ 0 with ∫_{[p,v̄]} dH_p = 1 and ∫_{[0,v̄]} ϕ_k dH_p ≥ 0 → finite measure H on ℝ with H([0,v̄]ᶜ) = 0, H([p,v̄]) = 1, Integrable (ϕ k) H and ∫ ϕ_k dH ≥ 0; reason: same measures
--   - encoding: λ_p = (λ₀(p), λ₁(p), …, λ_K(p)) ∈ ℝ × ℝ^K_+ → lam0 : ℝ and lam : Fin K → ℝ with lam k ≥ 0; reason: same multipliers
--   - encoding: real optimal values, infima and suprema → EReal values (⊤ for an unbounded supremum or an empty infimum); reason: Lean convention; avoids the junk value 0 of real sSup/sInf on unbounded or empty sets
--   - encoding: t(v) = ∫_0^v π(u)u du with π = Σ x_i δ(v − v_i) → pay v x w = Σ_{v_l ≤ w} x_l v_l; reason: closed form of the Dirac integral (p.ec8); the atom at w is included, the buyer buys at the posted price
--   - encoding: π ∈ Π_n → v : Fin n → ℝ monotone with values in [0,v̄], x ∈ stdSimplex ℝ (Fin n); reason: the paper's parametrization of Π_n (p.9); x_i ∈ [0,1] follows from the simplex
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, proof of Proposition 1, p.ec7 (PDF p.41)

import Mathlib
import Definitions.Def_SimpleMenus_pay
import Definitions.Def_SimpleMenus_Assumption1
import Definitions.Def_SimpleMenus_ambiguitySet
import Definitions.Def_SimpleMenus_IsPiece
import Definitions.Def_SimpleMenus_ConstraintQualification
import Definitions.Def_SimpleMenus_homogenizedValue
import Definitions.Def_SimpleMenus_pointwiseDualValue

open MeasureTheory Set

namespace SimpleMenus

/-- **Per-price strong duality** (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, proof of Proposition 1, p.ec7 = PDF p.41), with the
constraint qualification added: under Assumption 1 and `ConstraintQualification`, for every
`n`-level mechanism `(v, x)` and every price `p ∈ [0, v̄]`, the homogenized nature problem
`inf ∫ t dH_p` has the same value as its dual
`sup λ_0(p)` s.t. `Σ_k ϕ_k(w)λ_k(p) ≤ t(w)` on `[0, p)` and `λ_0(p) + Σ_k ϕ_k(w)λ_k(p) ≤ t(w)`
on `[p, v̄]`, `λ_0(p) ∈ ℝ`, `λ_k(p) ≥ 0`.

Formalization Note: values in `EReal`. `ConstraintQualification` is a correction: without it
the step is false (CE1, see its docstring: primal `c`, dual `0` at `p ∈ (0, c]`). -/
theorem prop_1_pointwise_duality (vbar : ℝ) {K n : ℕ} (phi : Fin K → ℝ → ℝ)
    (hA : Assumption1 vbar phi) (hCQ : ConstraintQualification vbar phi) (v x : Fin n → ℝ)
    (hv_mono : Monotone v) (hv_range : ∀ i, v i ∈ Icc 0 vbar) (hx : x ∈ stdSimplex ℝ (Fin n))
    (p : ℝ) (hp : p ∈ Icc 0 vbar) :
    homogenizedValue vbar phi v x p = pointwiseDualValue vbar phi v x p := by sorry

end SimpleMenus
