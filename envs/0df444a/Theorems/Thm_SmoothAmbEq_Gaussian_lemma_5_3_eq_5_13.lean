-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_lemma_5_3_eq_5_13
-- name    : SmoothAmbEq.Gaussian.lemma_5_3_eq_5_13
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T18:58:30.441646+00:00
-- url     : https://prove2.me/theorems/34a149cc-0615-49bc-b8bc-34e310b392a4
-- title:
--   Lemma 5.3, (5.13), pp. 16–17 — sup over Π of E[φ′(g^Z) 𝒜^{Z,π} g^Z | β_t = β] equals 0
-- statement:
--   Let $(m_1,\dots,m_6)$ solve the ODE system (5.10) on $[0,T]$ with $\zeta(t)^{-1}-\alpha m_3(t)>0$ for all $t\in[0,T]$, and let $g^z$ be the candidate value function (5.8)–(5.9),
--   $$g^z(t,x,\beta)=-\frac1k\exp\{-ke^{r(T-t)}x+f^z(t,\beta)\},\qquad f^z(t,\beta)=\tfrac12m_1\beta^2+m_2\beta z+\tfrac12m_3z^2+m_4\beta+m_5z+m_6 .$$
--   Then for every $(t,x,\beta)\in[0,T]\times\mathbb R^2$:
--
--   1. for every admissible strategy $\pi\in\Pi$ (Definition 5.1), the map $z\mapsto\phi'(g^z(t,x,\beta))\,\mathcal A^{z,\pi}g^z(t,x,\beta)$ is integrable under the posterior law $Z\mid\beta_t=\beta\sim N(\beta,\zeta(t))$;
--   2. (5.13) holds:
--   $$\sup_{\pi\in\Pi}\mathbf E\big[\phi'(g^Z(t,x,\beta))\,\mathcal A^{Z,\pi}g^Z(t,x,\beta)\mid\beta_t=\beta\big]=0,$$
--   the supremum being a least upper bound in $\mathbb R$.
--
--   Here $\mathcal A^{z,\pi}$ is the generator (5.7) evaluated at the action $p=\pi(t,x,\beta)$ and $\phi'(u)=(-u)^{\alpha-1}$. This is the (5.13) part of Lemma 5.3; the parts (5.11), (5.14), (5.15) are proved separately (they follow from (5.10) alone). In the paper, the expectation is a concave quadratic in $p$ whose maximiser, computed with Lemma C.2, is $\pi^*(t,x,\beta)$ of (5.12), and its value there is $0$ by (5.14).
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, pp. 16–17, Lemma 5.3, equation (5.13); proof in Appendix F (Proof of Lemma 5.3, final part)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

/-- Lemma 5.3, (5.13), pp. 16–17. Assume `(mᵢ)` solves (5.10) with `ζ(t)⁻¹ - αm₃(t) > 0` on
`[0, T]`, and let `g^z` be given by (5.8)–(5.9). Then for all `(t, x, β) ∈ [0, T] × ℝ²`,
`sup_{π ∈ Π} E[φ'(g^Z(t, x, β)) 𝒜^{Z,π} g^Z(t, x, β) | β_t = β] = 0`
(the expectation over `Z ∼ N(β, ζ(t))`, finite for every `π ∈ Π`; the supremum is a least upper
bound). -/
theorem lemma_5_3_eq_5_13 (M : Model) (c : Coeffs) (hc : SolvesODE510 M c) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) :
    ∀ t ∈ Icc 0 M.T, ∀ x β : ℝ,
      (∀ π : Strategy, Admissible M P W π →
        Integrable (fun z => M.φ' (gz M c z t x β) * gen M z (π t x β) (gz M c z) t x β)
          (posterior M t β)) ∧
      IsLUB {v : ℝ | ∃ π : Strategy, Admissible M P W π ∧
        v = ∫ z, M.φ' (gz M c z t x β) * gen M z (π t x β) (gz M c z) t x β
          ∂(posterior M t β)} 0 := by sorry

end SmoothAmbEq.Gaussian
