-- Prove2me | Theorems.Thm_SSLMultiView_mutualInfo_task_lower_bound
-- name    : SSLMultiView.mutualInfo_task_lower_bound
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T18:40:39.008722+00:00
-- url     : https://prove2.me/theorems/2015507a-f77a-4c2c-984e-030cc78e2c94
-- title:
--   Theorems 3 and 4 (proof, opening display): $I(Z_X;T)\ge I(Z_X;S)-I(X;S|T)-I(Z_X;X|S,T)$
-- statement:
--   Let $(X,S,T)$ have a joint probability mass function on finite sets, and let $Z_X=F_X(X)$ for a deterministic map $F_X$. Then
--
--   $$I(Z_X;T)\ge I(Z_X;S)-I(X;S\mid T)-I(Z_X;X\mid S,T).$$
--
--   The task-relevant information of any representation is bounded below by its information about the self-supervised signal, minus the compression gap $I(X;S\mid T)$ and the superfluous information $I(Z_X;X\mid S,T)$. This is the bound from which Theorem 3 follows.
-- source:
--   Tsai, Wu, Salakhutdinov and Morency, Self-supervised Learning from a Multi-view Perspective, ICLR 2021, arXiv:2006.05576v4, Appendix D, opening displays, p. 14

import Mathlib
import Definitions.Def_SSLMultiView_Basic

open Real

namespace SSLMultiView

theorem mutualInfo_task_lower_bound {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P) (F : X → Zs) :
    mutualInfo P (rep F) signalS - condMutualInfo P inputX signalS taskT -
        condMutualInfo P (rep F) inputX signalTask ≤ mutualInfo P (rep F) taskT := by sorry

end SSLMultiView
