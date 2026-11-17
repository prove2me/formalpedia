-- Prove2me | Theorems.Thm_TwoStageRnQ_impossibility_strict_inf
-- name    : TwoStageRnQ.impossibility_strict_inf
-- status  : Proved
-- author  : @beatlesmania
-- created : 2026-11-17T00:22:02.004377+00:00
-- url     : https://prove2.me/theorems/76fe493f-d0ef-4b25-b8e3-152fbcbb8aed
-- title:
--   Theorem 2: strict gap for the infimum over all classical controls and fixed-remainder initializations
-- statement:
--   **Theorem 2 with a strict gap for the whole classical class.** Let $\rho_\circ=(1+\sqrt3)/2$. For every $r<\rho_\circ$ there is an instance with $\lambda,L_1,L_2,h_1,h_2,p,K_1,K_2>0$ and $0<\mathrm{OPT}^{\mathrm{sh}}<\infty$ such that
--   $$r\,\mathrm{OPT}^{\mathrm{sh}}<\inf_{S,\,c}C^{\mathrm{sh}}_S(c),\qquad r\,\mathrm{OPT}^{\mathrm{sh}}<\inf_{S,\,c}C^{\mathrm{lot}}_S(c),$$
--   where the infima run over all demand environments $S$ and all classical controls $c=(R_1,R_2,Q,n,\rho)$ of the counter construction, and
--   $$r\,\mathrm{OPT}^{\mathrm{sh}}<\inf_{(S,\pi,c):\ \pi\text{ follows }c}C^{\mathrm{sh}}(\pi),\qquad r\,\mathrm{OPT}^{\mathrm{sh}}<\inf_{(S,\pi,c):\ \pi\text{ follows }c}C^{\mathrm{lot}}_{(Q,nQ)}(\pi),$$
--   where $\pi$ ranges over every shipment policy, on every demand environment, that follows the classical rule with controls $c=(R_1,R_2,Q,n,\rho)$ from a compatible initialization whose upstream remainder $W(0)\bmod Q$ equals the fixed control $\rho$ (`Rule.FollowsRnQ`). The benchmark is the shipment-accounted $\mathrm{OPT}^{\mathrm{sh}}$ in all four comparisons.
--
--   **Formalization Note** The paper states $\inf_{\Pi\in\mathcal P_{(R,nQ)}}C^{\mathrm{sh}}(\Pi)>r\,\mathrm{OPT}^{\mathrm{sh}}$ and the same with $C^{\mathrm{lot}}$. The earlier target `TwoStageRnQ.impossibility` asserts strictness separately on each demand environment; this target asserts it for the infimum over all environments, all controls including the remainder $\rho$, and all compatible initializations whose remainder equals that fixed $\rho$, and records $0<\mathrm{OPT}^{\mathrm{sh}}<\infty$ so that the ratio form is meaningful. Compatible initializations whose remainder varies with the outcome are covered by `TwoStageRnQ.impossibility_strict_inf_rand`, and `TwoStageRnQ.paper_rule_follows_rand` shows that every paper-compatible initialization belongs to that larger class.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Theorem 2, eq. (28); Appendix E; Appendices A.2-A.3.

import Definitions.Def_TwoStageRnQ_Rule

namespace TwoStageRnQ

theorem impossibility_strict_inf (r : ℝ) (hr : r < (1 + Real.sqrt 3) / 2) :
    ∃ P : Params, 0 < P.lam ∧ 0 < P.L1 ∧ 0 < P.L2 ∧ 0 < P.h1 ∧ 0 < P.h2 ∧ 0 < P.p ∧
      0 < P.K1 ∧ 0 < P.K2 ∧ 0 < OPTsh P ∧ OPTsh P < ⊤ ∧
      ENNReal.ofReal r * OPTsh P
        < ⨅ (S : DemandSpace P) (c : ClassicalControls), classicalShipCost P S c ∧
      ENNReal.ofReal r * OPTsh P
        < ⨅ (S : DemandSpace P) (c : ClassicalControls), classicalLotCost P S c ∧
      ENNReal.ofReal r * OPTsh P
        < ⨅ (S : DemandSpace P) (π : ShipmentPolicy P S) (c : ClassicalControls)
            (_ : Rule.FollowsRnQ S π c), π.shipCost ∧
      ENNReal.ofReal r * OPTsh P
        < ⨅ (S : DemandSpace P) (π : ShipmentPolicy P S) (c : ClassicalControls)
            (_ : Rule.FollowsRnQ S π c), π.lotCost (Rule.qc c) := by sorry

end TwoStageRnQ
