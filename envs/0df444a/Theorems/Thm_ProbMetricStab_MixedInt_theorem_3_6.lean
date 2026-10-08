-- Prove2me | Theorems.Thm_ProbMetricStab_MixedInt_theorem_3_6
-- name    : ProbMetricStab.MixedInt.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:02.512518+00:00
-- url     : https://prove2.me/theorems/c179e442-a322-4bad-8d8c-9b5d52e13cf1
-- title:
--   Theorem 3.6, (11), p. 15 — mixed-integer two-stage programs are Hölder stable w.r.t. d_{1,phk} with exponent 1/(1 + r/(p − 1))
-- statement:
--   Consider the mixed-integer two-stage program (9)
--   $$
--   \min\Big\{cx+\int_\Xi\Phi(h(\xi)-T(\xi)x)\,\mu(d\xi): x\in X\Big\},
--   $$
--   with $X\subseteq\mathbb R^m$ closed, $\Xi\subseteq\mathbb R^s$ a polyhedron, $\Phi$ the value function (10) of a second stage with $r$ equality constraints, and $h(\xi)$, $T(\xi)$ affine in $\xi$. Let (B1) (rational recourse matrices), (B2) (relatively complete recourse) and (B3) (dual feasibility) hold, and let $\mu\in\mathcal P_{p,K}(\Xi)$ for some constants $p>1$ and $K>0$. Assume that $S(\mu)$ is nonempty and that $\mathcal U\subseteq\mathbb R^m$ is an open bounded neighbourhood of $S(\mu)$.
--
--   Then there exist constants $L>0$, $\delta>0$ and $k\in\mathbb N$ such that, whenever $\nu\in\mathcal P_{p,K}(\Xi)$ and $d_{1,phk}(\mu,\nu)<\delta$, the values $v(\mu)$, $v_{\mathcal U}(\nu)$ are finite and
--   $$
--   |v(\mu)-v_{\mathcal U}(\nu)|\le L\,d_{1,phk}(\mu,\nu)^{\frac{1}{1+\frac{r}{p-1}}},\qquad
--   \emptyset\ne S_{\mathcal U}(\nu)\subseteq S(\mu)+\Psi\Big(L\,d_{1,phk}(\mu,\nu)^{\frac{1}{1+\frac{r}{p-1}}}\Big)\mathbb B,
--   $$
--   and $S_{\mathcal U}(\nu)$ is a CLM set for (9) with respect to $\mathcal U$. Here $\Psi(\eta)=\eta+\psi^{-1}(2\eta)$ is the modulus of Corollary 2.8, built from the growth function $\psi$ of (9) at $\mu$ on $X\cap\operatorname{cl}\mathcal U$.
--
--   The theorem identifies the polyhedral metric $d_{1,phk}$ as a canonical probability metric for linear mixed-integer two-stage stochastic programs: optimal values are Hölder continuous with exponent $(p-1)/(p-1+r)$, and localized solution sets are quantitatively upper semicontinuous.
--
--   **Formalization Note** $v(\mu)$ is the global optimal value and $v_{\mathcal U}(\nu)$, $S_{\mathcal U}(\nu)$ the localized ones, as printed. The constants $L$, $\delta$, $k$ depend on $\mu$, $\mathcal U$, $p$, $K$ and the data, never on $\nu$. The power is the real power of the (finite) real value of $d_{1,phk}(\mu,\nu)$, written as $1/(1+r/(p-1))$ as on the page. Finiteness of the two optimal values, implicit in the estimate, is stated explicitly. Measures in $\mathcal P_{p,K}(\Xi)$ are Borel probability measures on $\mathbb R^s$ concentrated on $\Xi$, and $\Psi$, $\psi^{-1}$ take values in $[0,\infty]$ (see the definition modules).
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 15, Theorem 3.6, (11)

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_Setting
open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt
theorem theorem_3_6 {m s r mh mb : ℕ} (P : MIProgram m s r mh mb)
    (hX : IsClosed P.X) (hΞ : IsPolyhedron P.Ξ)
    (hB1 : P.recourse.B1) (hB2 : P.B2) (hB3 : P.recourse.B3)
    {p K : ℝ} (hp : 1 < p) (hK : 0 < K)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ PpK P.Ξ p K)
    (hS : (solSet P.f0 P.X μ).Nonempty)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hSU : solSet P.f0 P.X μ ⊆ U) :
    ∃ L : ℝ, 0 < L ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ k : ℕ, ∀ ν ∈ PpK P.Ξ p K,
      d1phk k μ ν < ENNReal.ofReal δ →
        optVal P.f0 P.X μ ≠ ⊤ ∧ optVal P.f0 P.X μ ≠ ⊥ ∧
        locOptVal P.f0 P.X U ν ≠ ⊤ ∧ locOptVal P.f0 P.X U ν ≠ ⊥ ∧
        |(optVal P.f0 P.X μ).toReal - (locOptVal P.f0 P.X U ν).toReal| ≤
          L * (d1phk k μ ν).toReal ^ (1 / (1 + (r : ℝ) / (p - 1))) ∧
        (locSolSet P.f0 P.X U ν).Nonempty ∧
        locSolSet P.f0 P.X U ν ⊆
          addBall (solSet P.f0 P.X μ)
            (PsiCor28 P.f0 P.X U μ
              (ENNReal.ofReal (L * (d1phk k μ ν).toReal ^ (1 / (1 + (r : ℝ) / (p - 1)))))) ∧
        IsCLMSet P.f0 P.X U ν := by sorry
end ProbMetricStab.MixedInt
