-- Prove2me | Theorems.Thm_ProbMetricStab_MixedInt_estimate_12
-- name    : ProbMetricStab.MixedInt.estimate_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:21.451962+00:00
-- url     : https://prove2.me/theorems/96f79a64-95bd-4d3c-950b-825534a40ce0
-- title:
--   (12), p. 15 — d_{ℱ_𝒰}(μ, ν) ≤ C d_{1,phk}(μ, ν)^{1/(1 + r/(p − 1))} for small d_{1,phk}(μ, ν)
-- statement:
--   Consider program (9) under (B1)–(B3), with $X$ closed and $\Xi$ a polyhedron, and let $p>1$, $K>0$, $\mu\in\mathcal P_{p,K}(\Xi)$ and $\mathcal U\subseteq\mathbb R^m$ open and bounded. Then there are a constant $C>0$, a number $k\in\mathbb N$ and a threshold $\eta_0>0$ such that for every $\nu\in\mathcal P_{p,K}(\Xi)$ with $d_{1,phk}(\mu,\nu)<\eta_0$
--   $$
--   d_{\mathcal F_{\mathcal U}}(\mu,\nu)=\sup_{x\in X\cap\operatorname{cl}\mathcal U}\Big|\int_\Xi f_0(\xi,x)(\mu-\nu)(d\xi)\Big|\le C\,d_{1,phk}(\mu,\nu)^{\frac{1}{1+\frac{r}{p-1}}} .
--   $$
--
--   Here $r$ is the dimension of the second-stage right-hand side. The exponent equals $(p-1)/(p-1+r)$. The estimate bounds the minimal information distance of the mixed-integer program by the canonical polyhedral metric $d_{1,phk}$ and, combined with Theorems 2.2 and 2.3, yields Theorem 3.6.
--
--   **Formalization Note** "For sufficiently small $d_{1,phk}(\mu,\nu)$" is the threshold $\eta_0$; the number of faces $k$ is constructed in the proof and is existential, together with $C$. The power is the real power of the (finite) real value of $d_{1,phk}(\mu,\nu)$, and the bound on $d_{\mathcal F_{\mathcal U}}\in[0,\infty]$ is the corresponding nonnegative real. The hypotheses are those of Theorem 3.6 that the estimate uses; it does not need $S(\mu)\ne\emptyset$ or $S(\mu)\subseteq\mathcal U$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), pp. 15–16, proof of Theorem 3.6, (12)

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_Setting
open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt
theorem estimate_12 {m s r mh mb : ℕ} (P : MIProgram m s r mh mb)
    (hX : IsClosed P.X) (hΞ : IsPolyhedron P.Ξ)
    (hB1 : P.recourse.B1) (hB2 : P.B2) (hB3 : P.recourse.B3)
    {p K : ℝ} (hp : 1 < p) (hK : 0 < K)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ PpK P.Ξ p K)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hUo : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ ν ∈ PpK P.Ξ p K, d1phk k μ ν < ENNReal.ofReal η₀ →
        dFU P.f0 P.X U μ ν ≤
          ENNReal.ofReal (C * (d1phk k μ ν).toReal ^ (1 / (1 + (r : ℝ) / (p - 1)))) := by sorry
end ProbMetricStab.MixedInt
