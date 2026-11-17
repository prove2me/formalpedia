-- Prove2me | Theorems.Thm_TwoStageRnQ_exact_cost_classical
-- name    : TwoStageRnQ.exact_cost_classical
-- status  : Proved
-- author  : @beatlesmania
-- created : 2026-11-17T00:22:02.007242+00:00
-- url     : https://prove2.me/theorems/b3a04c86-848a-47b9-8505-05ed6080f1ac
-- title:
--   Proposition 1: exact cost of the classical $(R,nQ)$ rule
-- statement:
--   Proposition 1 (exact cost of the classical rule).
--
--   Let $\lambda>0$ and let $(\Omega,\mathcal F,\mathbb P,N)$ be any demand environment (two-sided Poisson history with an arbitrary initial count). For $R_1,R_2\in\mathbb Z$ and $Q,n\ge1$, the classical rule with zero initial upstream remainder has $$C^{\mathrm{lot}}=\frac{k_1}{Q}+\frac{k_2}{nQ}+I_{n,Q}(R_1+Q,\,R_2-R_1),$$ and $C^{\mathrm{sh}}\le C^{\mathrm{lot}}$.
--
--   **Formalization Note** The initial count is arbitrary, so the residue of $N$ modulo $nQ$ is uniform only in the limit; the long-run average absorbs the transient (paper, Lemma A.1).
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Proposition 1, eq. (9); Proposition A.1, Lemma A.1.

import Definitions.Def_TwoStageRnQ_Model

namespace TwoStageRnQ

theorem exact_cost_classical (P : Params) (hlam : 0 < P.lam) (S : DemandSpace P)
    (R1 R2 : ℤ) (Q n : ℕ+) :
    classicalLotCost P S ⟨(R1, R2, Q, n, 0), Q.pos⟩
        = ENNReal.ofReal (P.classicalFormula R1 R2 Q n) ∧
      classicalShipCost P S ⟨(R1, R2, Q, n, 0), Q.pos⟩
        ≤ classicalLotCost P S ⟨(R1, R2, Q, n, 0), Q.pos⟩ := by sorry

end TwoStageRnQ
