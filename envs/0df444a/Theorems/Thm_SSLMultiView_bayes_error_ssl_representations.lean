-- Prove2me | Theorems.Thm_SSLMultiView_bayes_error_ssl_representations
-- name    : SSLMultiView.bayes_error_ssl_representations
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T19:18:51.408194+00:00
-- url     : https://prove2.me/theorems/1b8dcc30-8c97-48ba-a85e-03865bdf0a77
-- title:
--   Theorem 4: Bayes error rates of self-supervised learned representations
-- statement:
--   Let $(X,S,T)$ have a joint probability mass function on finite sets with $|\mathcal T|\ge2$. Let representations $Z_X=F_X(X)$ take values in a finite set $\mathcal Z$ that admits an injective map $\mathcal X\to\mathcal Z$, and let $\epsilon_{\rm info}>0$ satisfy Assumption 1, $I(X;T\mid S)\le\epsilon_{\rm info}$. Let $Z_X^{\rm sup}$ be as in Definition 1 and $Z_X^{\rm ssl}$, $Z_X^{\rm ssl_{min}}$ as in Definition 2, with Bayes error rates $P_e^{\rm sup}$, $P_e^{\rm ssl}$, $P_e^{\rm ssl_{min}}$ for predicting $T$. Then there are $\bar P_e^{\rm ssl}$, $\bar P_e^{\rm ssl_{min}}$ with $P_e^{\rm ssl}={\rm Th}(\bar P_e^{\rm ssl})$, $P_e^{\rm ssl_{min}}={\rm Th}(\bar P_e^{\rm ssl_{min}})$, and each $\bar P\in\{\bar P_e^{\rm ssl},\bar P_e^{\rm ssl_{min}}\}$ satisfies
--
--   $$-\frac{\log(1-P_e^{\rm sup})+\log2}{\log|\mathcal T|}\le\bar P\le1-\exp\Big(-\big(\log2+P_e^{\rm sup}\log|\mathcal T|+\epsilon_{\rm info}\big)\Big).$$
--
--   The Bayes error of the self-supervised representations is controlled by that of the supervised one, and the upper bound improves as the multi-view redundancy $\epsilon_{\rm info}$ decreases.
--
--   **Formalization Note** The hypothesis $|\mathcal T|\ge2$ makes $\log|\mathcal T|>0$, so the lower bound does not divide by zero. The paper's setting of a categorical downstream task with at least two classes has it implicitly. In Lean $x/0=0$, and the statement would remain true for $|\mathcal T|=1$. The injectivity hypothesis is the one used in Theorem 1, whose chain of inequalities the proof invokes. It is part of the paper's implicit setting. Its necessity for Theorem 4 has not been established: no counterexample without it was found.
-- source:
--   Tsai, Wu, Salakhutdinov and Morency, Self-supervised Learning from a Multi-view Perspective, ICLR 2021, arXiv:2006.05576v4, Section 2.4, Theorem 4, p. 6 (restated as Theorem 8 with proof in Appendix D, p. 15); Assumption 1, Section 2.1, p. 3

import Mathlib
import Definitions.Def_SSLMultiView_Basic

open Real

namespace SSLMultiView

theorem bayes_error_ssl_representations {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P)
    (hZ : ∃ e : X → Zs, Function.Injective e) (hT : 2 ≤ Fintype.card T)
    (ε : ℝ) (hε : MultiViewAssumption P ε)
    (Fsup Fssl Fsslmin : X → Zs) (hsup : IsSupRep P Fsup)
    (hssl : IsSslRep P Fssl) (hsslmin : IsSslMinRep P Fsslmin) :
    (∃ Pbar : ℝ, bayesError P (rep Fssl) taskT = thresh (Fintype.card T) Pbar ∧
      -(Real.log (1 - bayesError P (rep Fsup) taskT) + Real.log 2) / Real.log (Fintype.card T : ℝ) ≤
        Pbar ∧
      Pbar ≤ 1 - Real.exp (-(Real.log 2 +
        bayesError P (rep Fsup) taskT * Real.log (Fintype.card T : ℝ) + ε))) ∧
    (∃ Pbar : ℝ, bayesError P (rep Fsslmin) taskT = thresh (Fintype.card T) Pbar ∧
      -(Real.log (1 - bayesError P (rep Fsup) taskT) + Real.log 2) / Real.log (Fintype.card T : ℝ) ≤
        Pbar ∧
      Pbar ≤ 1 - Real.exp (-(Real.log 2 +
        bayesError P (rep Fsup) taskT * Real.log (Fintype.card T : ℝ) + ε))) := by sorry

end SSLMultiView
