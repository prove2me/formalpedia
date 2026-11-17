-- Prove2me | Theorems.Thm_TwoStageRnQ_classical_attained
-- name    : TwoStageRnQ.classical_attained
-- status  : Proved
-- author  : @beatlesmania
-- created : 2026-11-17T00:21:59.412093+00:00
-- url     : https://prove2.me/theorems/00dee45e-a1e2-4d76-8378-d62d420a34f2
-- title:
--   Theorem 1 attainment
-- statement:
--   Attainment clause of Theorem 1 (Appendix D.5): if $\lambda,h_1,h_2,p>0$, some classical rule with zero initial upstream remainder has $C^{\mathrm{lot}}\le\mathcal J(k_1,k_2)$ on every demand environment.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Theorem 1; Appendix D.5.

import Definitions.Def_TwoStageRnQ_Model

namespace TwoStageRnQ

theorem classical_attained (P : Params) (hlam : 0 < P.lam) (hh1 : 0 < P.h1) (hh2 : 0 < P.h2)
    (hp : 0 < P.p) (S : DemandSpace P) :
    ∃ c : ClassicalControls, c.1.2.2.2.2 = 0 ∧
      classicalLotCost P S c ≤ ENNReal.ofReal (P.Jjoint P.k1 P.k2) := by sorry

end TwoStageRnQ
