-- Prove2me | Theorems.Thm_RiskPremiaDMP_Equivalence_proposition_1
-- name    : RiskPremiaDMP.Equivalence.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:20.150481+00:00
-- url     : https://prove2.me/theorems/4b95943b-19ef-4eb8-98ca-a699566f0ee3
-- title:
--   Proposition 1, p. 16 (PDF 17) — equivalence: the economy with risk premia and an artificial economy without risk premia have the same equilibrium tightness
-- statement:
--   **Proposition 1 (Equivalence result).** Consider the economy with risk premia: productivity $dy_t=-\kappa_yy_t\,dt+\sigma_y\,dB^{y,\mathcal P}_t$ (9), market price of risk $d\eta_t=\kappa_\eta(\bar\eta-\eta_t)\,dt+\sigma_\eta\,dB^{\eta,\mathcal P}_t$ (12), parameters $r_f,s,\beta,c,z$, standing assumptions $\kappa_y,\sigma_y,\kappa_\eta,\sigma_\eta>0$ and $\beta\in(0,1)$, and any vacancy-filling rate $q$. Let $a=\sigma_y\bar\eta/\kappa_y$, $y^{\mathcal Q}=y+a$, $\mu^{\mathcal Q}=\sigma_y(\bar\eta-\eta)/\kappa_y$ (21), and let the artificial economy without risk premia have $z^{\mathcal Q}=e^az$, $c^{\mathcal Q}=e^ac$ (23), parameters (27) $\kappa^{\mathcal Q}_y=\kappa_y$, $\sigma^{\mathcal Q}_y=\sigma_y$, $\kappa^{\mathcal Q}_\mu=\kappa_\eta$, $\sigma^{\mathcal Q}_\mu=\sigma_\eta\sigma_y/\kappa_y$, and the same $r_f,s,\beta,q$. Then:
--
--   1. the artificial economy satisfies the standing assumptions of §2.1;
--   2. for all functions $S,\theta$ on the original states and $S^{\mathcal Q},\theta^{\mathcal Q}$ on the artificial states related by (24),
--   $$S^{\mathcal Q}(y^{\mathcal Q},\mu^{\mathcal Q})=e^{a}S(y,\eta),\qquad\theta^{\mathcal Q}(y^{\mathcal Q},\mu^{\mathcal Q})=\theta(y,\eta),$$
--   $(S,\theta)$ is an equilibrium (19) of the economy with risk premia if and only if $(S^{\mathcal Q},\theta^{\mathcal Q})$ is an equilibrium (8) of the artificial economy; in particular the equilibrium tightness satisfies $\theta(y,\eta)=\theta^{\mathcal Q}(y^{\mathcal Q},\mu^{\mathcal Q})$;
--   3. if continuous paths $y,\eta$ solve (9) and (12) with driving paths $B^{y,\mathcal P},B^{\eta,\mathcal P}$, then $(y^{\mathcal Q}_t,\mu^{\mathcal Q}_t)$ solves the productivity equations (1) of the artificial economy, i.e. process (26), driven by $B^{y,\mathcal Q}_t=\int_0^t\eta_u\,du+B^{y,\mathcal P}_t$ (16) and by $-B^{\eta,\mathcal P}$.
--
--   The result says that risk premia affect labor-market tightness only through an altered productivity process and altered structural parameters: the economy with time-varying discount rates can be studied as a standard economy without risk premia.
--
--   **Formalization Note** Equilibria are the PDE characterizations (8) and (19), with $C^2$ surpluses; the Feynman–Kac step from the value functions to these PDEs and the Girsanov step making $B^{y,\mathcal Q}$ a Brownian motion under the risk-neutral measure are not formalized, and the dynamics are stated pathwise in integral form. The hypothesis $\sigma_y>0$ is added: the map (21b) is invertible only if $\sigma_y\neq0$. The value (22) $\mathbb E^{\mathcal Q}[y_t]=-a$ is taken as given. The equivalence is stated in both directions; the paper derives the forward direction.
-- source:
--   Mitra, Seo & Xu, High Discounts and Low Fundamental Surplus, FRB Atlanta Working Paper 2021-22 (Sept. 2021), p. 16 (PDF 17), Proposition 1, with (21)–(27) on pp. 14–15 (PDF 15–16)

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

namespace RiskPremiaDMP.Equivalence

theorem proposition_1 (P : RPParams) (hP : P.Standing) (q : ℝ → ℝ) :
    (artificial P).Standing ∧
    (∀ S θ SQ θQ : ℝ → ℝ → ℝ,
      (∀ y η : ℝ, SQ (toYQ P y) (toMuQ P η) = Real.exp (shift P) * S y η) →
      (∀ y η : ℝ, θQ (toYQ P y) (toMuQ P η) = θ y η) →
      (IsEquilibriumRP P q S θ ↔ IsEquilibriumNoRP (artificial P) q SQ θQ)) ∧
    (∀ y η BP Bη : ℝ → ℝ, Continuous y → Continuous η →
      SolvesPhysicalY P y BP → SolvesMPR P η Bη →
      SolvesProductivity (artificial P) (fun t => toYQ P (y t)) (fun t => toMuQ P (η t))
        (riskNeutralBM η BP) (fun t => -Bη t)) := by sorry

end RiskPremiaDMP.Equivalence
