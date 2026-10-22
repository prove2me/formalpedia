-- Prove2me | Theorems.Thm_RobustOpt2009_MatrixChance_theorem_B_5_1
-- name    : RobustOpt2009.MatrixChance.theorem_B_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:48.721481+00:00
-- url     : https://prove2.me/theorems/a1e9283e-a691-4270-b8a7-48cde26bf4ca
-- title:
--   Theorem B.5.1 — Gaussian dilation of closed convex sets
-- statement:
--   Let $\gamma_m=N(0,I_m)$ and let $Q\subseteq\mathbb R^m$ be closed and convex with $\gamma_m(Q)\ge\chi>1/2$. Write $q(p)=\operatorname{ErfInv}(p)$ and $T=\operatorname{Erf}$ for the upper standard normal tail. Then $q(1-\chi)>0$ and $Q$ contains the centered Euclidean ball of radius $q(1-\chi)$. If it contains a centered ball of real radius $r\ge q(1-\chi)$, then for every $\alpha\ge1$,
--   $$\gamma_m((\alpha Q)^c)\le T(q(1-\chi)+(\alpha-1)r)\le T(\alpha q(1-\chi))\le\tfrac12 e^{-\alpha^2q(1-\chi)^2/2}.$$
--   In addition, for every positive semidefinite covariance matrix $C$, every closed convex $Q$, and every $\alpha\ge1$, if $N(0,C)(Q^c)\le\delta<1/2$, then
--   $$N(0,C)((\alpha Q)^c)\le T(\alpha q(\delta))\le\tfrac12 e^{-\alpha^2q(\delta)^2/2}.$$
--   This includes both numbered clauses and the general-covariance consequence (B.5.4), including singular covariance matrices. Dilation means $\alpha Q=\{\alpha x:x\in Q\}$. The probability premise implies $\delta\ge0$.
--
--   **Formalization Note** Matrices and perturbation coordinates have positive finite dimensions, indexed from zero in Lean. Probabilities are real values of probability measures. The function $T(t)=\Pr\{G>t\}$ for $G\sim N(0,1)$ is the book's upper-tail Erf, not the usual error function. Its quantile $q(p)=\inf\{t\in\overline{\mathbb R}:T(t)\le p\}$ is extended by $q(0)=+\infty$ and $q(1)=-\infty$; $T(+\infty)=0$ and $e^{-\infty^2/2}=0$. This makes the probability-one endpoint, not specified by (2.3.22), explicit without removing it. Finite arguments give exactly the displayed source formulas. In the first clause, a ball of infinite radius means all of $\mathbb R^m$. At $\chi=1$ the first conclusion thus asserts $Q=\mathbb R^m$; the additional finite-radius hypothesis in the second clause cannot then hold. The zero-failure case $\delta=0$ in the covariance consequence is retained.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem B.5.1, printed p. 508 (PDF p. 534), including (B.5.2)–(B.5.4).

import Definitions.Def_RobustOpt2009_MatrixChance_Setting

open MeasureTheory ProbabilityTheory

namespace RobustOpt2009.MatrixChance

theorem theorem_B_5_1 {m : ℕ} [NeZero m] :
    (∀ (Q : Set (EuclideanSpace ℝ (Fin m))) (χ : ℝ),
      IsClosed Q → Convex ℝ Q → (1 / 2 : ℝ) < χ →
      χ ≤ ((stdGaussian (EuclideanSpace ℝ (Fin m))) Q).toReal →
      0 < tailQuantile (1 - χ) ∧
      {x : EuclideanSpace ℝ (Fin m) | (‖x‖ : EReal) ≤ tailQuantile (1 - χ)} ⊆ Q ∧
      (∀ r : ℝ, tailQuantile (1 - χ) ≤ (r : EReal) →
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r ⊆ Q →
        ∀ α : ℝ, 1 ≤ α →
          ((stdGaussian (EuclideanSpace ℝ (Fin m))) ((fun x => α • x) '' Q)ᶜ).toReal ≤
            normalTail (tailQuantile (1 - χ) + (((α - 1) * r : ℝ) : EReal)) ∧
          normalTail (tailQuantile (1 - χ) + (((α - 1) * r : ℝ) : EReal)) ≤
            normalTail ((α : EReal) * tailQuantile (1 - χ)) ∧
          normalTail ((α : EReal) * tailQuantile (1 - χ)) ≤
            (1 / 2) * gaussianEnvelope ((α : EReal) * tailQuantile (1 - χ)))) ∧
    (∀ (C : Matrix (Fin m) (Fin m) ℝ), C.PosSemidef →
      ∀ (Q : Set (EuclideanSpace ℝ (Fin m))) (δ α : ℝ),
        IsClosed Q → Convex ℝ Q → δ < (1 / 2 : ℝ) → 1 ≤ α →
        ((multivariateGaussian 0 C) Qᶜ).toReal ≤ δ →
        ((multivariateGaussian 0 C) ((fun x => α • x) '' Q)ᶜ).toReal ≤
          normalTail ((α : EReal) * tailQuantile δ) ∧
        normalTail ((α : EReal) * tailQuantile δ) ≤
          (1 / 2) * gaussianEnvelope ((α : EReal) * tailQuantile δ)) := by sorry

end RobustOpt2009.MatrixChance
