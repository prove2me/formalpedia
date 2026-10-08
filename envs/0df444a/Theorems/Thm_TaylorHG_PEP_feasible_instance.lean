-- Prove2me | Theorems.Thm_TaylorHG_PEP_feasible_instance
-- name    : TaylorHG.PEP.feasible_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:16.575988+00:00
-- url     : https://prove2.me/theorems/15587b30-c0ff-42e2-9013-ca4563ef96a3
-- title:
--   Section 3.3 — SDP point gives a function instance
-- statement:
--   Any feasible SDP pair $(G,v)$ with $\operatorname{rank}G\leq d$ is realized by a function $f\in\mathcal F_{\mu,L}(\mathbb R^d)$, a minimizer $x_*$, and a fixed-step run $x$. The run begins within radius $R$ and has exactly the SDP objective:
--
--   $$P_{b,C}(f,x_*,x)=b^\top v+\operatorname{Tr}(CG).$$
--
--   This is the reconstruction direction of the paper's exact correspondence.
--
--   **Formalization Note** $L$ is finite, $R\geq0$, and $C$ is symmetric. Nonnegative radius is necessary because the SDP records a squared-radius constraint.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 13, §3.3, paragraph after the compact formulation

import Mathlib
import Definitions.Def_TaylorHG_PEP_SDP

namespace TaylorHG.PEP

theorem feasible_instance {N : ℕ} (μ L : NNReal) (hμL : μ < L)
    (R : ℝ) (hR : 0 ≤ R) (H : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (hC : C.IsSymm)
    (d : ℕ) (G : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)
    (fv : Fin (N + 1) → ℝ) (hfeas : SdpFeasible μ L R H G fv)
    (hrank : G.rank ≤ d) :
    ∃ (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (xstar : EuclideanSpace ℝ (Fin d))
      (x : Fin (N + 1) → EuclideanSpace ℝ (Fin d)),
      FClass μ (L : ENNReal) f ∧ (∀ y, f xstar ≤ f y) ∧
      IsFixedStepRun H f x ∧ ‖x 0 - xstar‖ ≤ R ∧
      criterion b C f xstar x = b ⬝ᵥ fv + (C * G).trace := by sorry

end TaylorHG.PEP
