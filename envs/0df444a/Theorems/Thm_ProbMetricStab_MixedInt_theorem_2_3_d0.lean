-- Prove2me | Theorems.Thm_ProbMetricStab_MixedInt_theorem_2_3_d0
-- name    : ProbMetricStab.MixedInt.theorem_2_3_d0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:48.65798+00:00
-- url     : https://prove2.me/theorems/d0f6d317-a3b1-47e7-8b88-c364b59d9956
-- title:
--   Theorem 2.3 for d = 0, p. 8 — ∅ ≠ S_𝒰(ν) ⊆ S(μ) + Ψ(L̂ d_{ℱ_𝒰}(μ, ν))𝔹 for all ν ∈ 𝒫_{ℱ_𝒰}
-- statement:
--   Under the hypotheses of Theorem 2.2 with $d=0$ ($X$ nonempty and closed, $\Xi$ closed, $f$ a normal integrand, $\mathcal U$ open and bounded, $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$, $\emptyset\ne S(\mu)\subseteq\mathcal U$), there is a constant $\hat L\ge1$ such that for each $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$
--   $$
--   \emptyset\ne S_{\mathcal U}(\nu)\subseteq S(\mu)+\Psi\big(\hat L\,d_{\mathcal F_{\mathcal U}}(\mu,\nu)\big)\mathbb B ,
--   $$
--   where $\Psi(\eta)=\eta+\psi^{-1}(\eta)$, $\psi(\tau)=\inf\{\int_\Xi f(\xi,x)\mu(d\xi)-v(\mu): d(x,S(\mu))\ge\tau,\ x\in X\cap\operatorname{cl}\mathcal U\}$ is the growth function of the problem on $\operatorname{cl}\mathcal U$, and $\psi^{-1}(t)=\sup\{\tau\ge0:\psi(\tau)\le t\}$.
--
--   The theorem converts the value estimate of Theorem 2.2 into a quantitative upper semicontinuity of the localized solution sets, with a modulus governed by the growth of the objective near $S(\mu)$.
--
--   **Formalization Note** For $d=0$ the feasible set $M_{\mathcal U}(\mu)$ in $\psi$ is $X\cap\operatorname{cl}\mathcal U$. The page states (6) "for each $\nu\in\mathcal P_{\mathcal F,\mathcal U}$"; for $d=0$ this is correct as printed (the proof ends: "In case that $d=0$ we may choose $\hat x=\tilde x$, $\hat a=1$ and $L_\mu=0$"), so no $\delta$ appears. The paper's "min" in $\psi$ is read as an infimum ($+\infty$ when no point of $X\cap\operatorname{cl}\mathcal U$ is $\tau$-far from $S(\mu)$); $\psi^{-1}$ and $\Psi$ take values in $[0,\infty]$, and $\hat L\,d_{\mathcal F_{\mathcal U}}$ is a product in $[0,\infty]$. $S(\mu)+R\mathbb B$ is the Minkowski sum with the closed ball of radius $R$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 8, Theorem 2.3, (6), with d = 0 (last sentence of the proof)

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_ObjectiveStability
open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt
theorem theorem_2_3_d0 {m s : ℕ}
    (Ξ : Set (EuclideanSpace ℝ (Fin s))) (hΞ : IsClosed Ξ)
    (X : Set (EuclideanSpace ℝ (Fin m))) (hX : IsClosed X) (hXne : X.Nonempty)
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (hf : ProbMetricStab.TwoStage.IsNormalIntegrand Ξ f)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ PFU Ξ f X U)
    (hS : (solSet f X μ).Nonempty) (hSU : solSet f X μ ⊆ U) :
    ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ ν ∈ PFU Ξ f X U,
      (locSolSet f X U ν).Nonempty ∧
      locSolSet f X U ν ⊆
        addBall (solSet f X μ) (PsiThm23 f X U μ (ENNReal.ofReal Lhat * dFU f X U μ ν)) := by sorry
end ProbMetricStab.MixedInt
