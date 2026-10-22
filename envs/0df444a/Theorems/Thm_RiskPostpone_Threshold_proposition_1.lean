-- Prove2me | Theorems.Thm_RiskPostpone_Threshold_proposition_1
-- name    : RiskPostpone.Threshold.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:29.251285+00:00
-- url     : https://prove2.me/theorems/366bca56-3c18-41f8-b8aa-6cb404b32ec6
-- title:
--   Proposition 1 — ex ante optimal quantity d(p)/δ above the threshold price p̃, no production below (c > 0 or l > 0)
-- statement:
--   Work in the random-yield model with its standing assumptions and assume $c>0$ or $l>0$. Fix $\eta\in(0,1]$ and a price $p\in[c/\mu,p_0]$, and set the threshold sales price
--   $$
--   \tilde p=\min\Big\{p_0,\ \frac{c\eta}{\int_l^{G^{-1}(\eta)}\xi\,dG(\xi)}\Big\}.
--   $$
--   Then:
--
--   1. $\tilde p\ge c/\mu$.
--   2. If $p\ge\tilde p$, an inflation factor $\delta\in[l,u]$ with $\int_l^{\delta}\xi\,dG(\xi)=c\eta/p$ exists, and for every such $\delta$ the quantity $q_a^*(p)=d(p)/\delta\ge0$ maximizes $q\mapsto\Pi_a(p,q)$ over $q\ge0$, with
--   $$
--   \Pi_a(p,q_a^*(p))=p\,d(p)\Big(1-\frac{G(\delta)}{\eta}\Big).
--   $$
--   3. If $p<\tilde p$, the quantity $0$ maximizes $\Pi_a(p,\cdot)$ over $q\ge0$ and the maximum is $0$.
--   4. $\delta$ decreases in $p$: if $p\le p'$ in $[c/\mu,p_0]$ and $\delta,\delta'\in[l,u]$ solve the equation at $(\eta,p)$ and $(\eta,p')$, then $\delta'\le\delta$.
--   5. $\delta$ increases in $\eta$ and $d(p)/\delta$ decreases in $\eta$: if $\eta\le\eta'\le1$ and $\delta,\delta'\in[l,u]$ solve the equation at $(\eta,p)$ and $(\eta',p)$, then $\delta\le\delta'$ and $d(p)/\delta'\le d(p)/\delta$.
--
--   The proposition solves the inner problem of the ex ante firm: it produces at price $p$ exactly when $p$ exceeds $\tilde p$.
--
--   **Formalization Note** The paper's standing assumption $c\le p_0\mu$ allows $c=0$; with $c=0$ and $l=0$ the inflation factor is $\delta=0$, $d(p)/\delta$ is undefined and the CVaR increases in $q$ without a maximum, so the statement assumes $c>0$ or $l>0$ (exactly the cases where $\delta>0$). "Optimal" is a maximizer over $q\ge0$ of the CVaR objective; the paper's density $g$ is not used. "$q_a^*$ decreases in $\eta$" is stated for the formula $d(p)/\delta$ in the producing regime.
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), p. 9, Proposition 1

import Mathlib
import Definitions.Def_RiskPostpone_Threshold_Setting

open MeasureTheory Set

namespace RiskPostpone.Threshold

/-- Proposition 1 (p. 9): the ex ante firm's optimal quantity at a fixed price `p ∈ [c/µ, p0]`.
With `p̃ = min{p0, cη / ∫_l^{G⁻¹(η)} ξ dG(ξ)}`:
(0) `p̃ ≥ c/µ`;
(a) if `p ≥ p̃`, an inflation factor `δ ∈ [l,u]` with `∫_l^δ ξ dG(ξ) = cη/p` exists, and for every
such `δ` the quantity `q* = d(p)/δ ≥ 0` maximizes `Π_a(p, ·)` over `q ≥ 0` with value
`p·d(p)·(1 − G(δ)/η)`;
(b) if `p < p̃`, `q = 0` maximizes `Π_a(p, ·)` over `q ≥ 0` with value `0`;
(c) `δ` decreases in `p`; (d) `δ` increases in `η` and `d(p)/δ` decreases in `η`.
The case `c = 0`, `l = 0` is excluded (there the inflation factor is `δ = 0`, `d(p)/δ` is undefined
and the CVaR increases in `q` without a maximum): `c > 0` or `l > 0`. -/
theorem proposition_1 (M : Model) (hM : M.Standing) (hc : 0 < M.c ∨ 0 < M.l)
    (η : ℝ) (hη : η ∈ Ioc (0 : ℝ) 1) (p : ℝ) (hp : p ∈ Icc (M.c / M.mean) M.p0) :
    M.c / M.mean ≤ min M.p0 (M.c * η / ∫ ξ in Icc M.l (M.quantile η), ξ ∂M.ν) ∧
    (min M.p0 (M.c * η / ∫ ξ in Icc M.l (M.quantile η), ξ ∂M.ν) ≤ p →
      (∃ δ ∈ Icc M.l M.u, ∫ ξ in Icc M.l δ, ξ ∂M.ν = M.c * η / p) ∧
      ∀ δ ∈ Icc M.l M.u, ∫ ξ in Icc M.l δ, ξ ∂M.ν = M.c * η / p →
        0 ≤ M.d p / δ ∧ IsMaxOn (fun q => M.PiA η p q) (Ici 0) (M.d p / δ) ∧
        M.PiA η p (M.d p / δ) = p * M.d p * (1 - M.G δ / η)) ∧
    (p < min M.p0 (M.c * η / ∫ ξ in Icc M.l (M.quantile η), ξ ∂M.ν) →
      IsMaxOn (fun q => M.PiA η p q) (Ici 0) 0 ∧ M.PiA η p 0 = 0) ∧
    (∀ p' ∈ Icc (M.c / M.mean) M.p0, p ≤ p' → ∀ δ ∈ Icc M.l M.u, ∀ δ' ∈ Icc M.l M.u,
      ∫ ξ in Icc M.l δ, ξ ∂M.ν = M.c * η / p → ∫ ξ in Icc M.l δ', ξ ∂M.ν = M.c * η / p' →
        δ' ≤ δ) ∧
    (∀ η' ∈ Ioc (0 : ℝ) 1, η ≤ η' → ∀ δ ∈ Icc M.l M.u, ∀ δ' ∈ Icc M.l M.u,
      ∫ ξ in Icc M.l δ, ξ ∂M.ν = M.c * η / p → ∫ ξ in Icc M.l δ', ξ ∂M.ν = M.c * η' / p →
        δ ≤ δ' ∧ M.d p / δ' ≤ M.d p / δ) := by sorry

end RiskPostpone.Threshold
