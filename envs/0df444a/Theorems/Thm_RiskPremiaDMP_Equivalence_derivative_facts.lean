-- Prove2me | Theorems.Thm_RiskPremiaDMP_Equivalence_derivative_facts
-- name    : RiskPremiaDMP.Equivalence.derivative_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:01.251993+00:00
-- url     : https://prove2.me/theorems/d1eafd7f-969c-4b4d-b633-5687a5e31415
-- title:
--   §3, p. 15 (PDF 16), facts used for (25a) — S_y, S_yy, S_η, S_ηη in terms of the partial derivatives of S^Q
-- statement:
--   Consider the economy with risk premia under its standing assumptions, with shift $a=\sigma_y\bar\eta/\kappa_y=-\mathbb E^{\mathcal Q}[y_t]$ and state maps $y^{\mathcal Q}=y+a$, $\mu^{\mathcal Q}=\sigma_y(\bar\eta-\eta)/\kappa_y$ (21). Let $S^{\mathcal Q}(y^{\mathcal Q},\mu^{\mathcal Q})$ be twice continuously differentiable and let $S(y,\eta)$ be related to it by (24a),
--   $$S^{\mathcal Q}(y^{\mathcal Q},\mu^{\mathcal Q})=e^{a}S(y,\eta)\quad\text{for all }(y,\eta).$$
--   Then at every $(y,\eta)$, with the derivatives of $S^{\mathcal Q}$ evaluated at $(y^{\mathcal Q},\mu^{\mathcal Q})$,
--   $$S_y=e^{-a}S^{\mathcal Q}_{y^{\mathcal Q}},\quad S_{yy}=e^{-a}S^{\mathcal Q}_{y^{\mathcal Q}y^{\mathcal Q}},\quad S_\eta=-\frac{\sigma_y}{\kappa_y}e^{-a}S^{\mathcal Q}_{\mu^{\mathcal Q}},\quad S_{\eta\eta}=\frac{\sigma_y^2}{\kappa_y^2}e^{-a}S^{\mathcal Q}_{\mu^{\mathcal Q}\mu^{\mathcal Q}}.$$
--   Here $e^{-a}=\exp(\mathbb E^{\mathcal Q}[y_t])$ as in the paper.
--
--   These are the chain-rule identities that turn the risk-neutral generator $\mathscr L^{\mathcal Q}$ applied to $S$ into $e^{-a}$ times the generator $\mathscr L^{\mathcal P}$ of the artificial economy applied to $S^{\mathcal Q}$.
--
--   **Formalization Note** $C^2$ regularity of $S^{\mathcal Q}$ is a hypothesis (the paper's functions are implicitly smooth); without it `deriv` returns junk values.
-- source:
--   Mitra, Seo & Xu, High Discounts and Low Fundamental Surplus, FRB Atlanta Working Paper 2021-22 (Sept. 2021), p. 15 (PDF 16), §3, the facts used to derive (25a)

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

namespace RiskPremiaDMP.Equivalence

theorem derivative_facts (P : RPParams) (hP : P.Standing) (S SQ : ℝ → ℝ → ℝ)
    (hSQ : ContDiff ℝ 2 (Function.uncurry SQ))
    (h24a : ∀ y η : ℝ, SQ (toYQ P y) (toMuQ P η) = Real.exp (shift P) * S y η) (y η : ℝ) :
    d1 S y η = Real.exp (-shift P) * d1 SQ (toYQ P y) (toMuQ P η) ∧
      d11 S y η = Real.exp (-shift P) * d11 SQ (toYQ P y) (toMuQ P η) ∧
      d2 S y η = -(P.σy / P.κy) * Real.exp (-shift P) * d2 SQ (toYQ P y) (toMuQ P η) ∧
      d22 S y η
        = P.σy ^ 2 / P.κy ^ 2 * Real.exp (-shift P) * d22 SQ (toYQ P y) (toMuQ P η) := by sorry

end RiskPremiaDMP.Equivalence
