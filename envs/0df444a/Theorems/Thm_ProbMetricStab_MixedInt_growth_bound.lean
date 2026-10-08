-- Prove2me | Theorems.Thm_ProbMetricStab_MixedInt_growth_bound
-- name    : ProbMetricStab.MixedInt.growth_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:07.292741+00:00
-- url     : https://prove2.me/theorems/d016cb19-ffcd-4ae2-83c5-f5696d5ab3e8
-- title:
--   Proof of Theorem 3.6, p. 15 — |f₀(ξ, x)| ≤ ‖c‖‖x‖ + α(‖h(ξ)‖ + ‖T(ξ)‖‖x‖) + β, and 𝒫₁(Ξ) ⊆ 𝒫_{ℱ_𝒰}(Ξ)
-- statement:
--   Consider program (9) under (B1)–(B3), with integrand $f_0(\xi,x)=cx+\Phi(h(\xi)-T(\xi)x)$. There are constants $\alpha>0$ and $\beta>0$ such that
--
--   1. $|\Phi(t)-\Phi(\tilde t)|\le\alpha\|t-\tilde t\|+\beta$ for all $t,\tilde t\in\mathcal T$ (the estimate of Lemma 3.5);
--   2. with the same $\alpha,\beta$, for each pair $(\xi,x)\in\Xi\times X$ the value $f_0(\xi,x)$ is finite and
--   $$
--   |f_0(\xi,x)|\le\|c\|\|x\|+\alpha\big(\|h(\xi)\|+\|T(\xi)\|\|x\|\big)+\beta ;
--   $$
--   3. for every bounded $\mathcal U\subseteq\mathbb R^m$, every measure with a finite first moment belongs to the domain of the minimal information distance: $\mathcal P_1(\Xi)\subseteq\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$, where $\mathcal F_{\mathcal U}=\{f_0(\cdot,x):x\in X\cap\operatorname{cl}\mathcal U\}$.
--
--   This is the step that lets Theorem 2.2 be applied with $d=0$ and the distance $d_{\mathcal F_{\mathcal U}}$ on $\mathcal P_1(\Xi)$.
--
--   **Formalization Note** The page writes "it holds that $\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)\subseteq\mathcal P_1(\Xi)$" and concludes "Theorem 2.2 applies with $d=0$ and the distance $d_{\mathcal F_{\mathcal U}}$ on $\mathcal P_1(\Xi)$". The growth estimate proves, and the conclusion uses, the inclusion $\mathcal P_1(\Xi)\subseteq\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$; that direction is the one stated. $\mathcal U$ is assumed bounded, as it is in Theorem 3.6. $\|T(\xi)\|$ is the operator norm. The pair $(\alpha,\beta)$ is shared between items 1 and 2, which is how the proof obtains the bound from Lemma 3.5 (with $\tilde t=0$ and $\Phi(0)=0$).
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 15, proof of Theorem 3.6, first paragraph (estimate of |f₀(ξ, x)| and 𝒫_{ℱ_𝒰}(Ξ) vs. 𝒫₁(Ξ))

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_Setting
open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt
theorem growth_bound {m s r mh mb : ℕ} (P : MIProgram m s r mh mb)
    (hB1 : P.recourse.B1) (hB2 : P.B2) (hB3 : P.recourse.B3) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      (∀ t ∈ P.recourse.Tset, ∀ t' ∈ P.recourse.Tset,
        |(P.recourse.Phi t).toReal - (P.recourse.Phi t').toReal| ≤ α * ‖t - t'‖ + β) ∧
      (∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, P.f0 ξ x ≠ ⊤ ∧ P.f0 ξ x ≠ ⊥ ∧
        |(P.f0 ξ x).toReal| ≤ ‖P.c‖ * ‖x‖ + α * (‖P.h ξ‖ + ‖P.T ξ‖ * ‖x‖) + β) ∧
      (∀ U : Set (EuclideanSpace ℝ (Fin m)), Bornology.IsBounded U →
        Pp P.Ξ 1 ⊆ PFU P.Ξ P.f0 P.X U) := by sorry
end ProbMetricStab.MixedInt
