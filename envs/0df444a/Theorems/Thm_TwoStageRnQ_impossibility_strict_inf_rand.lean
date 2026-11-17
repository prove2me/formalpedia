-- Prove2me | Theorems.Thm_TwoStageRnQ_impossibility_strict_inf_rand
-- name    : TwoStageRnQ.impossibility_strict_inf_rand
-- status  : Proved
-- author  : @beatlesmania
-- created : 2026-11-17T00:22:11.536642+00:00
-- url     : https://prove2.me/theorems/8996945a-d578-4572-9ec3-2d95983175ca
-- title:
--   Theorem 2: strict gap for the whole classical class, remainder varying by outcome
-- statement:
--   **Theorem 2 with a strict gap for the whole classical class, the upstream remainder varying by outcome.** Let $\rho_\circ=(1+\sqrt3)/2$. For every $r<\rho_\circ$ there is an instance with $\lambda,L_1,L_2,h_1,h_2,p,K_1,K_2>0$ and $0<\mathrm{OPT}^{\mathrm{sh}}<\infty$ such that
--   $$r\,\mathrm{OPT}^{\mathrm{sh}}<\inf_{S,\,c}C^{\mathrm{sh}}_S(c),\qquad r\,\mathrm{OPT}^{\mathrm{sh}}<\inf_{S,\,c}C^{\mathrm{lot}}_S(c),$$
--   $$r\,\mathrm{OPT}^{\mathrm{sh}}<\inf C^{\mathrm{sh}}(\pi),\qquad r\,\mathrm{OPT}^{\mathrm{sh}}<\inf C^{\mathrm{lot}}_{(Q,nQ)}(\pi).$$
--   The first two infima run over all demand environments and all classical controls of the counter construction. The last two run over every demand environment $S$, every shipment policy $\pi$ and all fixed controls $(R_1,R_2,Q,n)$ such that $\pi$ follows the classical rule from a compatible initialization whose upstream remainder is any time-0 random variable (`RuleRand.FollowsRnQRand`). The benchmark is $\mathrm{OPT}^{\mathrm{sh}}$ in all four comparisons, and the class contains a policy whose costs are finite in both accountings, so the strict inequalities are not satisfied by an empty infimum.
--
--   **Formalization Note** This extends `TwoStageRnQ.impossibility_strict_inf`, whose policy infima cover compatible initializations with a fixed remainder (part of the controls). Together with `TwoStageRnQ.paper_rule_follows_rand` it covers every compatible initialization of the paper, with fixed or outcome-dependent remainder.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Theorem 2, eq. (28); Appendix E; Appendices A.2-A.3 (compatible initialization, Lemma A.2).

import Definitions.Def_TwoStageRnQ_RuleRand

namespace TwoStageRnQ

theorem impossibility_strict_inf_rand (r : ℝ) (hr : r < (1 + Real.sqrt 3) / 2) :
    ∃ P : Params, 0 < P.lam ∧ 0 < P.L1 ∧ 0 < P.L2 ∧ 0 < P.h1 ∧ 0 < P.h2 ∧ 0 < P.p ∧
      0 < P.K1 ∧ 0 < P.K2 ∧ 0 < OPTsh P ∧ OPTsh P < ⊤ ∧
      ENNReal.ofReal r * OPTsh P
        < ⨅ (S : DemandSpace P) (c : ClassicalControls), classicalShipCost P S c ∧
      ENNReal.ofReal r * OPTsh P
        < ⨅ (S : DemandSpace P) (c : ClassicalControls), classicalLotCost P S c ∧
      ENNReal.ofReal r * OPTsh P
        < ⨅ (S : DemandSpace P) (π : ShipmentPolicy P S) (R1 : ℤ) (R2 : ℤ) (Q : ℕ+)
            (n : ℕ+) (_ : RuleRand.FollowsRnQRand S π R1 R2 Q n), π.shipCost ∧
      ENNReal.ofReal r * OPTsh P
        < ⨅ (S : DemandSpace P) (π : ShipmentPolicy P S) (R1 : ℤ) (R2 : ℤ) (Q : ℕ+)
            (n : ℕ+) (_ : RuleRand.FollowsRnQRand S π R1 R2 Q n), π.lotCost (Q, n * Q) ∧
      ∃ (S : DemandSpace P) (π : ShipmentPolicy P S) (R1 R2 : ℤ) (Q n : ℕ+),
        RuleRand.FollowsRnQRand S π R1 R2 Q n ∧ π.shipCost < ⊤ ∧ π.lotCost (Q, n * Q) < ⊤ := by sorry

end TwoStageRnQ
