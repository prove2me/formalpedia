-- Prove2me | Theorems.Thm_SSLMultiView_determinism_cond_indep
-- name    : SSLMultiView.determinism_cond_indep
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T18:02:29.690136+00:00
-- url     : https://prove2.me/theorems/6b0dd777-2b0e-409c-8d38-275398814df3
-- title:
--   Lemma 1: determinism gives conditional independence given the input
-- statement:
--   Let $(X,S,T)$ have a joint probability mass function on finite sets, and let $Z_X=F_X(X)$ for a deterministic map $F_X$, so that $P(Z_X\mid X)$ is a Dirac mass. Then
--
--   $$T\perp Z_X\mid X,\qquad S\perp Z_X\mid X,\qquad (S,T)\perp Z_X\mid X.$$
--
--   This is the conditional independence the paper uses in every proof: the representation carries no information about the signal or the task beyond what the input carries.
--
--   **Formalization Note** The paper says the two conditional independences induce "a Markov chain $S\leftrightarrow T\leftrightarrow X\rightarrow Z_X$". Read literally, the link $S\leftrightarrow T\leftrightarrow X$ would assert $S\perp X\mid T$, which does not follow from determinism and is not assumed. The statement therefore includes the joint conditional independence $(S,T)\perp Z_X\mid X$, which is the "$X\rightarrow Z_X$" link that the proofs use.
-- source:
--   Tsai, Wu, Salakhutdinov and Morency, Self-supervised Learning from a Multi-view Perspective, ICLR 2021, arXiv:2006.05576v4, Appendix B, Lemma 1 (Determinism), p. 12

import Mathlib
import Definitions.Def_SSLMultiView_Basic

open Real

namespace SSLMultiView

theorem determinism_cond_indep {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P) (F : X → Zs) :
    CondIndep P taskT (rep F) inputX ∧ CondIndep P signalS (rep F) inputX ∧
      CondIndep P signalTask (rep F) inputX := by sorry

end SSLMultiView
