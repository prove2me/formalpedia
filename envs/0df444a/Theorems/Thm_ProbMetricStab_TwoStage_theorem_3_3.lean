-- Prove2me | Theorems.Thm_ProbMetricStab_TwoStage_theorem_3_3
-- name    : ProbMetricStab.TwoStage.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:11.478019+00:00
-- url     : https://prove2.me/theorems/44fb78a0-cf2d-4708-8549-cd813bcc7e66
-- title:
--   Theorem 3.3, p. 13 — linear two-stage programs: |v(μ) − v(ν)| ≤ Lζ₂(μ, ν) and ∅ ≠ S(ν) ⊆ S(μ) + Ψ(Lζ₂(μ, ν))𝔹
-- statement:
--   Consider the linear two-stage stochastic program with fixed recourse in its first-stage form
--
--   $$\min\Big\{\int_\Xi f_0(\xi,x)\,\mu(d\xi):x\in X\Big\},$$
--
--   where $X\subseteq\mathbb R^m$ is a nonempty polyhedron, $\Xi\subseteq\mathbb R^s$ is a polyhedron, $f_0(\xi,x)=cx+\Phi(q(\xi),h(\xi)-T(\xi)x)$ (and $+\infty$ off the domain), $\Phi$ is the second-stage optimal value, and $q,h,T$ depend affine linearly on $\xi$. Let $v(\nu)$ and $S(\nu)$ be the optimal value and solution set when $\mu$ is replaced by $\nu$. Assume
--
--   1. (A1): $h(\xi)-T(\xi)x\in\operatorname{pos}W$ and $q(\xi)\in D$ for all $(\xi,x)\in\Xi\times X$;
--   2. (A2): $\mu\in\mathcal P(\Xi)$ has a finite second moment;
--   3. $S(\mu)$ is nonempty and $\mathcal U$ is an open, bounded neighbourhood of $S(\mu)$.
--
--   Then there exist constants $L>0$ and $\delta>0$ such that, whenever $\nu\in\mathcal P_2(\Xi)$ and $\zeta_2(\mu,\nu)<\delta$, the values $v(\mu)$, $v(\nu)$ are finite and
--
--   $$|v(\mu)-v(\nu)|\le L\,\zeta_2(\mu,\nu),\qquad\emptyset\ne S(\nu)\subseteq S(\mu)+\Psi\big(L\,\zeta_2(\mu,\nu)\big)\mathbb B,$$
--
--   where $\zeta_2$ is the Fortet–Mourier metric of order 2, $\mathbb B$ the closed unit ball, and $\Psi(\eta)=\eta+\psi^{-1}(2\eta)$ with $\psi$ the growth function of the problem near $S(\mu)$ on $X\cap\operatorname{cl}\mathcal U$, as in Corollary 2.8.
--
--   The theorem identifies $\zeta_2$ as a canonical metric for linear two-stage programs: optimal values are Lipschitz and solution sets upper Lipschitz-type stable with respect to it, under relatively complete recourse, dual feasibility and finite second moments only.
--
--   **Formalization Note** The constants $L,\delta$ depend on $\mu$, $\mathcal U$ and the data, not on $\nu$. The finiteness of both optimal values is stated explicitly, since the paper's real inequality asserts it. $\zeta_2$ and $\Psi$ take values in $[0,\infty]$; "$\zeta_2(\mu,\nu)<\delta$" compares in $[0,\infty]$ and the value inequality uses the real value of $\zeta_2$, which is finite under that hypothesis. The inclusion is written pointwise: every $x\in S(\nu)$ has a $y\in S(\mu)$ with $\|x-y\|\le\Psi(L\zeta_2(\mu,\nu))$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 13, Theorem 3.3

import Mathlib
import Definitions.Def_ProbMetricStab_TwoStage_Model

namespace ProbMetricStab.TwoStage

/-- Theorem 3.3 (p. 13): for the linear two-stage program (8), let (A1) and (A2) hold, `S(μ)` be
nonempty and `𝒰` an open bounded neighbourhood of `S(μ)`. Then there are `L > 0` and `δ > 0`
such that, whenever `ν ∈ 𝒫₂(Ξ)` and `ζ₂(μ, ν) < δ`, `v(μ), v(ν)` are finite with
`|v(μ) − v(ν)| ≤ L ζ₂(μ, ν)` and `∅ ≠ S(ν) ⊆ S(μ) + Ψ(L ζ₂(μ, ν)) 𝔹`, with `Ψ` as in
Corollary 2.8. -/
theorem theorem_3_3 {m s r mbar : ℕ} (P : Data m s r mbar) (hP : P.Standing) (hA1 : P.A1)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin s))) (hA2 : P.A2 μ)
    (U : Set (EuclideanSpace ℝ (Fin m)))
    (hS : (S P.X P.Ξ P.f0 μ).Nonempty) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hSU : S P.X P.Ξ P.f0 μ ⊆ U) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ ∀ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin s)),
      ν ∈ Pp P.Ξ 2 → zetaP P.Ξ 2 μ ν < ENNReal.ofReal δ →
        (v P.X P.Ξ P.f0 μ ≠ ⊤ ∧ v P.X P.Ξ P.f0 μ ≠ ⊥ ∧
          v P.X P.Ξ P.f0 ν ≠ ⊤ ∧ v P.X P.Ξ P.f0 ν ≠ ⊥ ∧
          |(v P.X P.Ξ P.f0 μ).toReal - (v P.X P.Ξ P.f0 ν).toReal| ≤
            L * (zetaP P.Ξ 2 μ ν).toReal) ∧
        (S P.X P.Ξ P.f0 ν).Nonempty ∧
        ∀ x ∈ S P.X P.Ξ P.f0 ν, ∃ y ∈ S P.X P.Ξ P.f0 μ,
          edist x y ≤ Psi P.X P.Ξ P.f0 μ U (ENNReal.ofReal L * zetaP P.Ξ 2 μ ν) := by sorry

end ProbMetricStab.TwoStage
