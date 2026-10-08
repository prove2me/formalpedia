-- Prove2me | Theorems.Thm_TaylorHG_PEP_instance_feasible
-- name    : TaylorHG.PEP.instance_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:54.681985+00:00
-- url     : https://prove2.me/theorems/74ee1ef9-9c81-43e8-bdd5-3426bf0fd481
-- title:
--   Section 3.3 — function instance gives an SDP point
-- statement:
--   A function in $\mathcal F_{\mu,L}$, a minimizer, and a fixed-step run starting within radius $R$ yield a feasible SDP pair. With columns $[\nabla f(x_0),\ldots,\nabla f(x_N),x_0-x_*]$ and values $v_i=f(x_i)-f(x_*)$, its Gram matrix has rank at most $d$ and
--
--   $$b^\top v+\operatorname{Tr}(CG)=P_{b,C}(f,x_*,x).$$
--
--   This gives the direction from an actual optimization run to the finite SDP.
--
--   **Formalization Note** $L$ is finite and $C$ is symmetric as in Theorem 5. The minimizer is explicit.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 13, §3.3, paragraph after the compact formulation

import Mathlib
import Definitions.Def_TaylorHG_PEP_SDP

namespace TaylorHG.PEP

theorem instance_feasible {d N : ℕ} (μ L : NNReal) (hμL : μ < L)
    (R : ℝ) (H : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (hC : C.IsSymm)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : FClass μ (L : ENNReal) f)
    (xstar : EuclideanSpace ℝ (Fin d)) (hmin : ∀ y, f xstar ≤ f y)
    (x : Fin (N + 1) → EuclideanSpace ℝ (Fin d))
    (hrun : IsFixedStepRun H f x) (hR : ‖x 0 - xstar‖ ≤ R) :
    let G := gramOf (Fin.snoc (fun i => gradient f (x i)) (x 0 - xstar))
    let fv := fun i => f (x i) - f xstar
    SdpFeasible μ L R H G fv ∧ G.rank ≤ d ∧
      b ⬝ᵥ fv + (C * G).trace = criterion b C f xstar x := by sorry

end TaylorHG.PEP
