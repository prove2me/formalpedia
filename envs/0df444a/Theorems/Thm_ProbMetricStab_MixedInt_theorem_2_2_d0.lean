-- Prove2me | Theorems.Thm_ProbMetricStab_MixedInt_theorem_2_2_d0
-- name    : ProbMetricStab.MixedInt.theorem_2_2_d0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:55.857441+00:00
-- url     : https://prove2.me/theorems/67b55299-10cd-4446-9e2d-d279f99c8061
-- title:
--   Theorem 2.2 for d = 0, p. 6 — S_𝒰 Berge usc at μ, |v(μ) − v_𝒰(ν)| ≤ d_{ℱ_𝒰}(μ, ν) for all ν, CLM sets near μ
-- statement:
--   Let $X\subseteq\mathbb R^m$ be nonempty and closed, $\Xi\subseteq\mathbb R^s$ closed, and $f:\Xi\times\mathbb R^m\to\overline{\mathbb R}$ a normal integrand, and consider the program $\min\{\int_\Xi f(\xi,x)\nu(d\xi): x\in X\}$ (no probabilistic constraints, $d=0$). Let $\mathcal U\subseteq\mathbb R^m$ be open and bounded, let $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$, and assume that $S(\mu)$ is nonempty and $S(\mu)\subseteq\mathcal U$. Then
--
--   1. the multifunction $S_{\mathcal U}$ is (Berge) upper semicontinuous at $\mu$ with respect to $d_{\mathcal F_{\mathcal U}}$: for every open $\mathcal O\supseteq S_{\mathcal U}(\mu)$ there is $\varepsilon>0$ with $S_{\mathcal U}(\nu)\subseteq\mathcal O$ whenever $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$ and $d_{\mathcal F_{\mathcal U}}(\mu,\nu)<\varepsilon$;
--   2. for **every** $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$ the values $v(\mu)$ and $v_{\mathcal U}(\nu)$ are finite and
--   $$
--   |v(\mu)-v_{\mathcal U}(\nu)|\le d_{\mathcal F_{\mathcal U}}(\mu,\nu)
--   $$
--   (estimate (4) with $L=1$);
--   3. there is $\delta>0$ such that $S_{\mathcal U}(\nu)$ is a CLM set with respect to $\mathcal U$ whenever $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$ and $d_{\mathcal F_{\mathcal U}}(\mu,\nu)<\delta$.
--
--   This is the general quantitative stability theorem of §2 in the objective-only case; Theorem 3.6 applies it to the mixed-integer integrand $f_0$ and then bounds $d_{\mathcal F_{\mathcal U}}$ by the canonical metric $d_{1,phk}$.
--
--   **Formalization Note** For $d=0$, conditions (ii) and (iii) of Theorem 2.2 are void and $M_{\mathcal U}(\nu)=X\cap\operatorname{cl}\mathcal U$. "Open bounded neighbourhood of $S(\mu)$" is: $\mathcal U$ open, bounded, $S(\mu)\subseteq\mathcal U$. The finiteness of $v(\mu)$ and $v_{\mathcal U}(\nu)$, implicit in (4), is stated explicitly so that the estimate compares real numbers; $d_{\mathcal F_{\mathcal U}}$ takes values in $[0,\infty]$ and the threshold $\delta$ is a positive real. The paper states the theorem for constraints $j=1,\dots,d$ in general; this item is its case $d=0$, restated in this mission's namespace.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 6, Theorem 2.2 with d = 0 (including its last sentence: "In case d = 0, the estimate (4) is valid with L = 1 and for all ν ∈ 𝒫_{ℱ_𝒰}")

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_ObjectiveStability
open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt
theorem theorem_2_2_d0 {m s : ℕ}
    (Ξ : Set (EuclideanSpace ℝ (Fin s))) (hΞ : IsClosed Ξ)
    (X : Set (EuclideanSpace ℝ (Fin m))) (hX : IsClosed X) (hXne : X.Nonempty)
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (hf : ProbMetricStab.TwoStage.IsNormalIntegrand Ξ f)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ PFU Ξ f X U)
    (hS : (solSet f X μ).Nonempty) (hSU : solSet f X μ ⊆ U) :
    (∀ O : Set (EuclideanSpace ℝ (Fin m)), IsOpen O → locSolSet f X U μ ⊆ O →
      ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ PFU Ξ f X U, dFU f X U μ ν < ENNReal.ofReal ε →
        locSolSet f X U ν ⊆ O) ∧
    (∀ ν ∈ PFU Ξ f X U,
      optVal f X μ ≠ ⊤ ∧ optVal f X μ ≠ ⊥ ∧ locOptVal f X U ν ≠ ⊤ ∧ locOptVal f X U ν ≠ ⊥ ∧
      ENNReal.ofReal |(optVal f X μ).toReal - (locOptVal f X U ν).toReal| ≤ dFU f X U μ ν) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ ν ∈ PFU Ξ f X U, dFU f X U μ ν < ENNReal.ofReal δ →
      IsCLMSet f X U ν) := by sorry
end ProbMetricStab.MixedInt
