-- Prove2me | Theorems.Thm_RiskPremiaDMP_Equivalence_rp_to_artificial
-- name    : RiskPremiaDMP.Equivalence.rp_to_artificial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:08.793975+00:00
-- url     : https://prove2.me/theorems/d6a440bc-d29a-46ea-8e4d-8cf87d68dfc3
-- title:
--   §3, p. 15 (PDF 16), (25a)–(25b) — substituting (21), (23), (24) into (19) gives the equilibrium (8) of the artificial economy
-- statement:
--   Consider the economy with risk premia under its standing assumptions and a vacancy-filling rate $q$. Let $(S,\theta)$ be an equilibrium of this economy, i.e. a $C^2$ solution of (19),
--   $$(r_f+s)S=e^y-z-\frac{\beta c}{1-\beta}\theta+\mathscr L^{\mathcal Q}S,\qquad c=(1-\beta)q(\theta)S,$$
--   and let $S^{\mathcal Q},\theta^{\mathcal Q}$ be related to $S,\theta$ by (24): $S^{\mathcal Q}(y^{\mathcal Q},\mu^{\mathcal Q})=e^{a}S(y,\eta)$ and $\theta^{\mathcal Q}(y^{\mathcal Q},\mu^{\mathcal Q})=\theta(y,\eta)$ for all $(y,\eta)$, with $a=\sigma_y\bar\eta/\kappa_y$ and the state maps (21). Then $(S^{\mathcal Q},\theta^{\mathcal Q})$ is an equilibrium (8) of the artificial economy, that is,
--   $$\begin{aligned}(r_f+s)S^{\mathcal Q}&=e^{y^{\mathcal Q}}-z^{\mathcal Q}-\frac{\beta c^{\mathcal Q}}{1-\beta}\theta^{\mathcal Q}+\mathscr L^{\mathcal P}[\kappa_y,\sigma_y,\kappa_\eta,\sigma_\eta\sigma_y/\kappa_y]S^{\mathcal Q},\qquad(25a)\\ c^{\mathcal Q}&=(1-\beta)q(\theta^{\mathcal Q})S^{\mathcal Q},\qquad(25b)\end{aligned}$$
--   at every state, with $z^{\mathcal Q}=e^az$, $c^{\mathcal Q}=e^ac$, and $S^{\mathcal Q}$ twice continuously differentiable.
--
--   This is the forward direction of the equivalence in Proposition 1.
--
--   **Formalization Note** $\sigma_y>0$ (part of the standing assumptions here) is what makes the state map onto, so that (25) holds at every state of the artificial economy.
-- source:
--   Mitra, Seo & Xu, High Discounts and Low Fundamental Surplus, FRB Atlanta Working Paper 2021-22 (Sept. 2021), pp. 14–15 (PDF 15–16), §3, (19), (21), (23), (24), (25a)–(25b)

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

namespace RiskPremiaDMP.Equivalence

theorem rp_to_artificial (P : RPParams) (hP : P.Standing) (q : ℝ → ℝ)
    (S θ SQ θQ : ℝ → ℝ → ℝ)
    (h24a : ∀ y η : ℝ, SQ (toYQ P y) (toMuQ P η) = Real.exp (shift P) * S y η)
    (h24b : ∀ y η : ℝ, θQ (toYQ P y) (toMuQ P η) = θ y η)
    (h19 : IsEquilibriumRP P q S θ) :
    IsEquilibriumNoRP (artificial P) q SQ θQ := by sorry

end RiskPremiaDMP.Equivalence
