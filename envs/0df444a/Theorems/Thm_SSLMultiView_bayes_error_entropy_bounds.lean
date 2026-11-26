-- Prove2me | Theorems.Thm_SSLMultiView_bayes_error_entropy_bounds
-- name    : SSLMultiView.bayes_error_entropy_bounds
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T18:52:13.811988+00:00
-- url     : https://prove2.me/theorems/63671648-2fe4-4d47-ad35-d55119c73f86
-- title:
--   Theorems 3 and 4 (proof): the Feder–Merhav and Fano bounds and the range of $P_e$
-- statement:
--   Let $(X,S,T)$ have a joint probability mass function on finite sets, let $Z_X=F_X(X)$ for a deterministic map $F_X$, and let $P_e=1-\sum_z\max_tP(Z_X=z,T=t)$ be the Bayes error rate of predicting $T$ from $Z_X$. Then
--
--   $$-\log(1-P_e)\le H(T\mid Z_X)\le\log2+P_e\log|\mathcal T|,\qquad 0\le P_e\le1-\frac1{|\mathcal T|}.$$
--
--   The left inequality is the bound the paper cites from Feder and Merhav (1994). The right inequality is the form of Fano's inequality that the paper cites from Cover and Thomas. The range of $P_e$ is the "feasible range" used at the end of the proofs of Theorems 3 and 4.
-- source:
--   Tsai, Wu, Salakhutdinov and Morency, Self-supervised Learning from a Multi-view Perspective, ICLR 2021, arXiv:2006.05576v4, Appendix D, proofs of Theorems 7 and 8 (= Theorems 3 and 4), pp. 14-15; Bayes error rate defined in Section 2.4, p. 6

import Mathlib
import Definitions.Def_SSLMultiView_Basic

open Real

namespace SSLMultiView

theorem bayes_error_entropy_bounds {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P) (F : X → Zs) :
    -Real.log (1 - bayesError P (rep F) taskT) ≤ condEntropy P taskT (rep F) ∧
      condEntropy P taskT (rep F) ≤
        Real.log 2 + bayesError P (rep F) taskT * Real.log (Fintype.card T : ℝ) ∧
      0 ≤ bayesError P (rep F) taskT ∧
      bayesError P (rep F) taskT ≤ 1 - 1 / (Fintype.card T : ℝ) := by sorry

end SSLMultiView
