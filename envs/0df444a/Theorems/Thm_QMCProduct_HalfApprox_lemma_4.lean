-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_lemma_4
-- name    : QMCProduct.HalfApprox.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:52.411867+00:00
-- url     : https://prove2.me/theorems/2ada8f4f-347e-41c2-98ef-ad527daeaea7
-- title:
--   Lemma 4, p. 12 — E[(Zu/‖Zu‖)·(Zv/‖Zv‖)] = F(k, u·v) for a k×d standard Gaussian matrix Z
-- statement:
--   Let $k\ge1$ and let $u,v$ be unit vectors in $\mathbb R^d$. Draw a $k\times d$ matrix $R$ whose entries are independent standard normal random variables. With $\operatorname{Unit}(x)=x/\|x\|$ for $x\ne0$,
--   $$\mathbb E\big[\operatorname{Unit}(Ru)\cdot\operatorname{Unit}(Rv)\big]=F(k,u\cdot v),$$
--   where $F$ is the hypergeometric function in equation (3). This gives the edge correlation of Algorithm 2.
--
--   **Formalization Note** The source implicitly uses a positive row count; Lean states $k\ge1$. At zero, `Unit` is set to zero, which affects no Gaussian expectation.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 12, Lemma 4 and equation (3)

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCProduct.HalfApprox

open MeasureTheory

/-- Lemma 4, p. 12 (from Briët, de Oliveira Filho and Vallentin). -/
theorem lemma_4 {k d : ℕ} (hk : 1 ≤ k)
    (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Fin k → Fin d → Ω → ℝ) (hR : IsStdGaussianMatrix P R) :
    (∫ ω, inner ℝ (unitVec (gaussianProject R ω u))
      (unitVec (gaussianProject R ω v)) ∂P) = F k (inner ℝ u v) := by sorry

end QMCProduct.HalfApprox
