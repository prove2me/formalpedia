-- Prove2me | Theorems.Thm_PGLandscape_GradDom_performance_difference
-- name    : PGLandscape.GradDom.performance_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:55.702176+00:00
-- url     : https://prove2.me/theorems/1fe2aa8e-266e-4a86-9502-3281b5755db8
-- title:
--   (29), App. D.1, p. 39 — performance difference: ℓ(π) − ℓ(π̄) = ∫ [T_π J_π̄ − J_π̄] dη_π
-- statement:
--   Let $\pi$ and $\bar\pi$ be measurable stationary policies, $\ell$ the normalized discounted loss, $J_{\bar\pi}$ the cost-to-go of $\bar\pi$, $T_\pi$ the Bellman operator of $\pi$ and $\eta_\pi$ the discounted state-occupancy measure of $\pi$. Then
--   $$\ell(\pi)-\ell(\bar\pi)=\int\big[T_\pi J_{\bar\pi}-J_{\bar\pi}\big]\,d\eta_\pi. \tag{29}$$
--
--   This is the cost, normalized-loss version of the performance difference lemma of Kakade and Langford (2002) on a general state space. It is the identity behind the policy gradient theorem (Lemma 6) and the on-average Bellman equation (Lemma 8).
--
--   **Formalization Note** Only the outer members of (29) are stated; the middle member, an expectation over the controlled chain, has no separate object in the formal setting and is the same quantity by the definition of $\eta_\pi$. The identity holds for all measurable policies, feasible or not. The page prints (3) and (4) without the factor $\gamma$; the factor is restored, as in (6), (7), Assumption 2 and every proof (without it $T$ has no fixed point $J^*$).
-- source:
--   arXiv:1906.01786v3, App. D.1, (29), p. 39

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.GradDom

open MeasureTheory ProbabilityTheory

/-- (29), App. D.1, p. 39 (outer members): the performance difference identity
`ℓ(π) − ℓ(π̄) = ∫ [T_π J_π̄ − J_π̄] dη_π` for measurable stationary policies `π`, `π̄`. -/
theorem performance_difference {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (π πbar : PGLandscape.Closure.MPolicy S A) :
    PGLandscape.Closure.loss M π - PGLandscape.Closure.loss M πbar =
      ∫ s, (PGLandscape.Closure.bellmanPi M π.1 (PGLandscape.Closure.costToGo M πbar) s - PGLandscape.Closure.costToGo M πbar s) ∂(PGLandscape.Closure.occupancy M π) := by sorry

end PGLandscape.GradDom
