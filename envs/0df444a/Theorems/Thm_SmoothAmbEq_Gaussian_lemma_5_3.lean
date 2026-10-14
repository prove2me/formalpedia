-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_lemma_5_3
-- name    : SmoothAmbEq.Gaussian.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:08.63364+00:00
-- url     : https://prove2.me/theorems/de459f83-88ea-417c-b656-7c3672d0bed5
-- title:
--   Lemma 5.3, pp. 16–17 — (5.11) and the equilibrium HJB conditions (5.13)–(5.15) for the candidate g^z and π*
-- statement:
--   Assume $(m_1,\dots,m_6)$ solves (5.10) and $\zeta(t)^{-1}-\alpha m_3(t)>0$ for all $t\in[0,T]$. Then
--   $$m_4=-rm_1-rm_2,\qquad m_5=-rm_2-rm_3.\qquad(5.11)$$
--   Let $\pi^*$ be given by (5.12) and $g^z$ by (5.8)–(5.9). Then for all $(t,x,\beta)\in[0,T]\times\mathbb R^2$ and $z\in\mathbb R$,
--   $$\sup_{\pi\in\Pi}\mathbb E\big[\phi'(g^Z(t,x,\beta))\,\mathcal A^{Z,\pi}g^Z(t,x,\beta)\mid\beta_t=\beta\big]=0,\qquad(5.13)$$
--   $$\mathcal A^{z,\pi^*}g^z(t,x,\beta)=0,\qquad(5.14)\qquad g^z(T,x,\beta)=-\frac1ke^{-kx}.\qquad(5.15)$$
--
--   These are the extended HJB conditions (condition (a) of the verification Theorem 4.5) for the closed-form candidate.
--
--   **Formalization Note** The expectation in (5.13) is over $Z\sim N(\beta,\zeta(t))$; its integrand is shown integrable for every $\pi\in\Pi$, and the supremum is stated as "$0$ is the least upper bound" of the set of values (a Lean `⨆` over an unbounded set would be $0$ by default). $\Pi$ refers to a fixed probability space with Brownian motion. The time derivative in $\mathcal A$ is taken within $[0,T]$, which makes (5.13)–(5.14) meaningful at $t=T$ (paper.md slip 6).
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, pp. 16–17, Lemma 5.3, (5.11)–(5.15)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

/-- Lemma 5.3, pp. 16–17. Assume `(mᵢ)` solves (5.10) with `ζ(t)⁻¹ - αm₃(t) > 0` on `[0, T]`.
Then (5.11) `m₄ = -rm₁ - rm₂`, `m₅ = -rm₂ - rm₃`; and with `g^z` of (5.8)–(5.9) and `π*` of
(5.12), for all `(t, x, β) ∈ [0, T] × ℝ²`:
(5.13) `sup_{π ∈ Π} E[φ'(g^Z(t, x, β)) 𝒜^{Z,π} g^Z(t, x, β) | β_t = β] = 0` (the expectation over
`Z ∼ N(β, ζ(t))`, finite for every `π ∈ Π`; the supremum is a least upper bound);
(5.14) `𝒜^{z,π*} g^z(t, x, β) = 0`; (5.15) `g^z(T, x, β) = -(1/k)e^{-kx}`. -/
theorem lemma_5_3 (M : Model) (c : Coeffs) (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    (∀ t ∈ Icc 0 M.T,
      c.m₄ t = -M.r * c.m₁ t - M.r * c.m₂ t ∧ c.m₅ t = -M.r * c.m₂ t - M.r * c.m₃ t) ∧
    (∀ t ∈ Icc 0 M.T, ∀ x β : ℝ,
      (∀ π : Strategy, Admissible M P W π →
        Integrable (fun z => M.φ' (gz M c z t x β) * gen M z (π t x β) (gz M c z) t x β)
          (posterior M t β)) ∧
      IsLUB {v : ℝ | ∃ π : Strategy, Admissible M P W π ∧
        v = ∫ z, M.φ' (gz M c z t x β) * gen M z (π t x β) (gz M c z) t x β
          ∂(posterior M t β)} 0) ∧
    (∀ z : ℝ, ∀ t ∈ Icc 0 M.T, ∀ x β : ℝ,
      gen M z (piStar M c t x β) (gz M c z) t x β = 0) ∧
    (∀ z x β : ℝ, gz M c z M.T x β = -(1 / M.k) * Real.exp (-M.k * x)) := by sorry

end SmoothAmbEq.Gaussian
