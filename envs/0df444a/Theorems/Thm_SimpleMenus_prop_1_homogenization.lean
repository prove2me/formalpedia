-- Prove2me | Theorems.Thm_SimpleMenus_prop_1_homogenization
-- name    : SimpleMenus.prop_1_homogenization
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:40.608412+00:00
-- url     : https://prove2.me/theorems/49bfc5d4-3fd5-46d0-ad6f-809757fe72bb
-- title:
--   Proof of Proposition 1, p.ec6 — homogenization: $\inf_{F\in\mathcal F}\mathrm{Rev}(\pi,F)/(1-F(p-))$ equals the linear program in $H_p$
-- statement:
--   Let $\pi$ be an $n$-level mechanism with price levels $v_1\le\dots\le v_n$ in $[0,\bar v]$ and probabilities $x$, let $t$ be its expected payment, and let $p\in[0,\bar v]$. Then nature's problem at the price $p$ has the same value as the homogenized linear program:
--
--   $$\inf_{F\in\mathcal F}\frac{\int_0^{\bar v}t\,dF}{1-F(p-)}\;=\;\inf\Bigl\{\int_0^{\bar v}t\,dH_p\;:\;H_p\ge0,\ \int_{[p,\bar v]}dH_p=1,\ \int_{[0,\bar v]}\phi_k\,dH_p\ge0\ \forall k\Bigr\}.$$
--
--   The substitution $H_p=F/(1-F(p-))$ removes the nonlinear denominator. This is the first step of the proof of Proposition 1.
--
--   **Formalization Note** No assumption on the $\phi_k$ is needed; values are extended reals.
--
--   Differences from the source:
--   - generalization: the step is made under Assumption 1 (standing in §2) → no assumption on the ϕ_k; reason: the substitution uses none; the statement specializes to the paper's
--   - generalization: k = 1, …, K → ϕ : Fin K → ℝ → ℝ with K = 0 allowed; reason: K = 0 is the set of all laws on [0,v̄]; every K ≥ 1 is included
--   - encoding: inf over dF ≥ 0 with ∫ dF = 1 of Rev(π,F)/(1 − F(p−)) → natureValue: infimum over F ∈ 𝓕 with F([p,∞)) > 0; reason: a law with 1 − F(p−) = 0 has an undefined ratio, and H_p = F/(1 − F(p−)) is defined only for the others; (EC.1) multiplies such laws out
--   - encoding: dH_p ≥ 0 with ∫_{[p,v̄]} dH_p = 1 and ∫_{[0,v̄]} ϕ_k dH_p ≥ 0 → finite measure H on ℝ with H([0,v̄]ᶜ) = 0, H([p,v̄]) = 1, Integrable (ϕ k) H and ∫ ϕ_k dH ≥ 0; reason: same measures
--   - encoding: real optimal values, infima and suprema → EReal values (⊤ for an unbounded supremum or an empty infimum); reason: Lean convention; avoids the junk value 0 of real sSup/sInf on unbounded or empty sets
--   - encoding: t(v) = ∫_0^v π(u)u du with π = Σ x_i δ(v − v_i) → pay v x w = Σ_{v_l ≤ w} x_l v_l; reason: closed form of the Dirac integral (p.ec8); the atom at w is included, the buyer buys at the posted price
--   - encoding: F ∈ P([0, v̄]), constraints ∫ ϕ_k dF ≥ 0 → Borel probability measure on ℝ with F([0,v̄]ᶜ) = 0, and Integrable (ϕ k) F in each constraint; reason: same laws; integrability holds for every such law when ϕ_k is bounded and piecewise monotone
--   - encoding: π ∈ Π_n → v : Fin n → ℝ monotone with values in [0,v̄], x ∈ stdSimplex ℝ (Fin n); reason: the paper's parametrization of Π_n (p.9); x_i ∈ [0,1] follows from the simplex
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, proof of Proposition 1, p.ec6 (PDF p.40)

import Mathlib
import Definitions.Def_SimpleMenus_pay
import Definitions.Def_SimpleMenus_rev
import Definitions.Def_SimpleMenus_ambiguitySet
import Definitions.Def_SimpleMenus_natureValue
import Definitions.Def_SimpleMenus_homogenizedValue

open MeasureTheory Set

namespace SimpleMenus

/-- **Homogenization** (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, proof of Proposition 1, p.ec6 = PDF p.40): for every `n`-level
mechanism `(v, x)` and every price `p ∈ [0, v̄]`, nature's problem
`inf_{F ∈ 𝓕} Rev(π, F) / (1 − F(p−))` has the same value as the linear program in
`H_p = F / (1 − F(p−))`: `inf ∫ t dH_p` over finite measures `H_p` on `[0, v̄]` with
`H_p([p, v̄]) = 1` and `∫ ϕ_k dH_p ≥ 0`.

Formalization Note: values in `EReal`; nature's infimum runs over the laws with
`1 − F(p−) > 0`. No assumption on the `ϕ_k` is made (the step holds for every family). -/
theorem prop_1_homogenization (vbar : ℝ) {K n : ℕ} (phi : Fin K → ℝ → ℝ) (v x : Fin n → ℝ)
    (hv_mono : Monotone v) (hv_range : ∀ i, v i ∈ Icc 0 vbar) (hx : x ∈ stdSimplex ℝ (Fin n))
    (p : ℝ) (hp : p ∈ Icc 0 vbar) :
    natureValue vbar phi v x p = homogenizedValue vbar phi v x p := by sorry

end SimpleMenus
