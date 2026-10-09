-- Prove2me | Theorems.Thm_SLQSolv_UnifConvex_completion_of_squares
-- name    : SLQSolv.UnifConvex.completion_of_squares
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:01.270623+00:00
-- url     : https://prove2.me/theorems/ebdebe96-8475-49e3-ae14-20088de9abf1
-- title:
--   Proof of Theorem 4.5, (ii) ⇒ (i), p. 2291 — J⁰(0, 0; u) = E∫⟨(R + DᵀPD)(u − ΘX⁽ᵘ⁾), u − ΘX⁽ᵘ⁾⟩ds
-- statement:
--   Assume (H1)–(H2). Let $P$ solve the Riccati equation (4.6) and suppose
--
--   $$R(s)+D(s)^\top P(s)D(s)\ \ge\ \lambda I\quad\text{a.e. }s\in[0,T]\qquad(4.27)$$
--
--   for some $\lambda>0$. Set $\Theta=-(R+D^\top PD)^{-1}(B^\top P+D^\top PC+S)$. For $u\in\mathcal U[0,T]$ let $X^{(u)}$ solve $dX^{(u)}=[AX^{(u)}+Bu]ds+[CX^{(u)}+Du]dW$, $X^{(u)}(0)=0$. Then
--
--   $$J^0(0,0;u)=\mathbb E\int_0^T\big\langle(R+D^\top PD)(u-\Theta X^{(u)}),\,u-\Theta X^{(u)}\big\rangle ds .$$
--
--   Together with (4.27) and Lemma 2.3 this gives the uniform convexity (4.2), i.e. the implication (ii) ⇒ (i) of Theorem 4.5.
--
--   **Formalization Note** $X^{(u)}$ is the state of Problem (SLQ)$^0$ from $(0,0)$. $\Theta$ is written with the matrix inverse, as printed; by (4.27) the matrix is invertible a.e.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §4, proof of Theorem 4.5, (ii) ⇒ (i), (4.27), pp. 2290–2291

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Iteration

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

/-- §4, proof of Theorem 4.5, (ii) ⇒ (i), p. 2291. If `P` solves the Riccati equation (4.6) with
(4.27) `R + DᵀPD ≥ λI` a.e. for some `λ > 0`, `Θ = −(R + DᵀPD)⁻¹(BᵀP + DᵀPC + S)`, and `X^{(u)}`
solves the homogeneous state equation from `(0, 0)`, then for every `u ∈ 𝒰[0, T]`
`J⁰(0, 0; u) = E∫₀ᵀ ⟨(R + DᵀPD)(u − ΘX^{(u)}), u − ΘX^{(u)}⟩ ds`. -/
theorem completion_of_squares {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω)
    (d : Data Ω n m) (h1 : H1 Bs d) (h2 : H2 Bs d)
    (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hP : IsRiccatiSol d P)
    (lam : ℝ) (hlam : 0 < lam)
    (h427 : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) d.T)),
      (sigmaR d P s.toNNReal - lam • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (u : ℝ≥0 → Ω → Fin m → ℝ) (hu : Adm Bs d 0 u) :
    J0 Bs d 0 0 u =
      ∫ ω, ∫ s in Icc (0 : ℝ) d.T,
        (sigmaR d P s.toNNReal *ᵥ (u s.toNNReal ω
            - thetaOf d P s.toNNReal *ᵥ state Bs d.hom 0 0 u s.toNNReal ω))
          ⬝ᵥ (u s.toNNReal ω - thetaOf d P s.toNNReal *ᵥ state Bs d.hom 0 0 u s.toNNReal ω)
        ∂volume ∂Bs.P := by sorry

end SLQSolv.UnifConvex
