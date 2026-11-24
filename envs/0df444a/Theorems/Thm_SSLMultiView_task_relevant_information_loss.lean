-- Prove2me | Theorems.Thm_SSLMultiView_task_relevant_information_loss
-- name    : SSLMultiView.task_relevant_information_loss
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T18:13:50.1818+00:00
-- url     : https://prove2.me/theorems/98faaa39-5fa5-42ee-aef6-ed765065a510
-- title:
--   Theorem 1: task-relevant information with a potential loss $\epsilon_{\rm info}$
-- statement:
--   Let $(X,S,T)$ have a joint probability mass function on finite sets $\mathcal X,\mathcal S,\mathcal T$. Let representations $Z_X=F_X(X)$ take values in a finite set $\mathcal Z$ that admits an injective map $\mathcal X\to\mathcal Z$. Let $\epsilon_{\rm info}>0$ satisfy Assumption 1, $I(X;T\mid S)\le\epsilon_{\rm info}$. Let $Z_X^{\rm sup}$, $Z_X^{\rm sup_{min}}$ be any representations as in Definition 1, and $Z_X^{\rm ssl}$, $Z_X^{\rm ssl_{min}}$ any representations as in Definition 2. Then
--
--   $$I(X;T)=I(Z_X^{\rm sup};T)=I(Z_X^{\rm sup_{min}};T)\ge I(Z_X^{\rm ssl};T)\ge I(Z_X^{\rm ssl_{min}};T)\ge I(X;T)-\epsilon_{\rm info}.$$
--
--   The supervised representations keep all the task-relevant information of the input. The self-supervised ones, trained without access to $T$, keep all of it up to the loss $\epsilon_{\rm info}$ allowed by the multi-view assumption.
--
--   **Formalization Note** The paper's proof uses that $I(Z_X;T)$ and $I(Z_X;S)$ attain their maxima $I(X;T)$ and $I(X;S)$, which requires the representation space to be able to encode the input. This is the hypothesis that an injective map $\mathcal X\to\mathcal Z$ exists. Without it the first equality fails, for example when $\mathcal Z$ has one point. The chain is stated as five separate relations.
-- source:
--   Tsai, Wu, Salakhutdinov and Morency, Self-supervised Learning from a Multi-view Perspective, ICLR 2021, arXiv:2006.05576v4, Section 2.2, Theorem 1, p. 3 (restated as Theorem 5 with proof in Appendix B, p. 13); Assumption 1, Section 2.1, p. 3; Definitions 1 and 2, Section 2.2, p. 3

import Mathlib
import Definitions.Def_SSLMultiView_Basic

open Real

namespace SSLMultiView

theorem task_relevant_information_loss {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P)
    (hZ : ∃ e : X → Zs, Function.Injective e) (ε : ℝ) (hε : MultiViewAssumption P ε)
    (Fsup Fsupmin Fssl Fsslmin : X → Zs) (hsup : IsSupRep P Fsup) (hsupmin : IsSupMinRep P Fsupmin)
    (hssl : IsSslRep P Fssl) (hsslmin : IsSslMinRep P Fsslmin) :
    mutualInfo P inputX taskT = mutualInfo P (rep Fsup) taskT ∧
      mutualInfo P (rep Fsup) taskT = mutualInfo P (rep Fsupmin) taskT ∧
      mutualInfo P (rep Fssl) taskT ≤ mutualInfo P (rep Fsupmin) taskT ∧
      mutualInfo P (rep Fsslmin) taskT ≤ mutualInfo P (rep Fssl) taskT ∧
      mutualInfo P inputX taskT - ε ≤ mutualInfo P (rep Fsslmin) taskT := by sorry

end SSLMultiView
