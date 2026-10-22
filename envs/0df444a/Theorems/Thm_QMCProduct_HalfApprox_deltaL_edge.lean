-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_deltaL_edge
-- name    : QMCProduct.HalfApprox.deltaL_edge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:21.933502+00:00
-- url     : https://prove2.me/theorems/3fe6aa68-f17c-413e-add2-394d9f9605f7
-- title:
--   Proof of Theorem 3, p. 19 — an edge adjacent to L earns 1/4 > µij/2
-- statement:
--   Let $\widetilde\rho$ be a level-2 pseudo-density, and use the threshold $\gamma=0.911$. Suppose $ik\in L$ is large and $ij$ is another graph edge with $j\ne k$. In Algorithm 4's output $\rho$, the edge $ij$ has energy exactly $1/4$, and its relaxed value is below $1/2$:
--   $$\operatorname{Tr}(H_{ij}\rho)=\frac14>\frac12\mu_{ij}.$$
--   This completes the edge classification in the proof of Theorem 3.
--
--   **Formalization Note** The statement covers every Gaussian outcome and computes the energy from the full matrix output. The large-edge membership is unordered, matching the source graph. Distinctness of $j$ and $k$ says that $ij$ is adjacent to, rather than identical with, $ik$.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 19, proof of Theorem 3, final displayed equation

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- The last displayed edge bound in the proof of Theorem 3, p. 19. -/
theorem deltaL_edge {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (hW : IsRoundingInput ρt W)
    {Ω : Type} (R : Fin 3 → Fin d → Ω → ℝ)
    (i j k : Fin n) (hij : G.Adj i j) (hjk : j ≠ k)
    (hik : inLarge G ρt (911 / 1000 : ℝ) i k) :
    (∀ ω, (hQMC i j * alg4State G ρt (911 / 1000 : ℝ) W R ω).trace.re = 1 / 4) ∧
      (1 / 2 : ℝ) * mu ρt i j < 1 / 4 := by sorry

end QMCProduct.HalfApprox
