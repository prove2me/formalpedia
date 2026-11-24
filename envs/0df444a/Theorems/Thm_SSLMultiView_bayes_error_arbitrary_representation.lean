-- Prove2me | Theorems.Thm_SSLMultiView_bayes_error_arbitrary_representation
-- name    : SSLMultiView.bayes_error_arbitrary_representation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T19:02:41.406375+00:00
-- url     : https://prove2.me/theorems/7e349f0f-7217-4559-93af-e609de8bdff8
-- title:
--   Theorem 3 (as proved): Bayes error rate of an arbitrary learned representation
-- statement:
--   Let $(X,S,T)$ have a joint probability mass function on finite sets, let $Z_X=F_X(X)$ for a deterministic map $F_X$, and let $P_e$ be the Bayes error rate of predicting $T$ from $Z_X$. With ${\rm Th}(x)=\min\{\max\{x,0\},1-1/|\mathcal T|\}$, there is $\bar P_e$ with $P_e={\rm Th}(\bar P_e)$ and
--
--   $$\bar P_e\le1-\exp\Big(-\big(H(T)+I(X;S\mid T)+I(Z_X;X\mid S,T)-I(Z_X;S)\big)\Big).$$
--
--   A representation with high information about the self-supervised signal and little task-irrelevant information therefore has a small Bayes error.
--
--   **Formalization Note** The printed Theorem 3 has the neural estimate $\hat I^{(n)}_{\theta^*}(Z_X;S)$ of Proposition 1 plus an unspecified term $O\big(\sqrt{(d+\log(1/\delta))/n}\big)$ in place of $I(Z_X;S)$, and holds with probability at least $1-\delta$. Proposition 1 gives neither the network family nor the constant in $O(\cdot)$, so that version cannot be stated precisely. The statement here is the deterministic bound that the proof establishes before Proposition 1 is applied. The paper writes $I(Z;X\mid S,T)$ for $I(Z_X;X\mid S,T)$.
-- source:
--   Tsai, Wu, Salakhutdinov and Morency, Self-supervised Learning from a Multi-view Perspective, ICLR 2021, arXiv:2006.05576v4, Section 2.4, Theorem 3, p. 6; proof of Theorem 7 (= Theorem 3) in Appendix D, p. 15, stated before the estimation step

import Mathlib
import Definitions.Def_SSLMultiView_Basic

open Real

namespace SSLMultiView

theorem bayes_error_arbitrary_representation {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P) (F : X → Zs) :
    ∃ Pbar : ℝ, bayesError P (rep F) taskT = thresh (Fintype.card T) Pbar ∧
      Pbar ≤ 1 - Real.exp (-(entropy P taskT + condMutualInfo P inputX signalS taskT +
        condMutualInfo P (rep F) inputX signalTask - mutualInfo P (rep F) signalS)) := by sorry

end SSLMultiView
