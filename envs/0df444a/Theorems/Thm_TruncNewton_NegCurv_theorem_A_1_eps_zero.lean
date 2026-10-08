-- Prove2me | Theorems.Thm_TruncNewton_NegCurv_theorem_A_1_eps_zero
-- name    : TruncNewton.NegCurv.theorem_A_1_eps_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:07:05.755465+00:00
-- url     : https://prove2.me/theorems/2e994c11-b96d-4464-bd24-48c0ce7ef2b6
-- title:
--   Theorem A.1, (A.2) and (A.5), p. 206, at ε = 0 as used in the proof of Theorem 2.4 — CG conjugacy and Krylov spans
-- statement:
--   Let $H$ be a symmetric linear operator on $\mathbb{R}^n$, let $g\in\mathbb{R}^n$, and let $d_0,d_1,\dots$ be the conjugate gradient directions of the TNCG minor iteration for $H$ and $g$ (Steps 1–4, p. 194). Let $k\ge 0$ and suppose that the curvature along every direction up to $k$ is positive:
--
--   $$
--   d_i^{\mathsf T}Hd_i>0,\qquad i=0,1,\dots,k.
--   $$
--
--   Then the directions are mutually $H$-conjugate and span the Krylov space of $g$:
--
--   1. (A.2) $\;d_i^{\mathsf T}Hd_j=0$ for $i\ne j$, $i,j=0,1,\dots,k$;
--   2. (A.5) $\;[d_0,d_1,\dots,d_k]=[g,Hg,\dots,H^kg]$, where $[\cdot]$ denotes the linear span.
--
--   This is the part of the Hestenes–Stiefel relations of Theorem A.1 that the proof of Theorem 2.4 uses: conjugacy with positive curvature, and the identification of the directions' span with the Krylov space, are what let one pass from the CG run to the spectral statement of Theorem A.5.
--
--   **Formalization Note** The paper states Theorem A.1 under "Let $\varepsilon>0$" with hypothesis $d_i^{\mathsf T}Hd_i>\varepsilon\delta_i$; the proof of Theorem 2.4 applies (A.2) and (A.5) at $\varepsilon=0$, where that hypothesis reads $d_i^{\mathsf T}Hd_i>0$, and this item states exactly that case. The page prints (A.5) as $[d_0,\dots,d_k]=[g,Hg,\dots,H^{k-1}g]$, with $k+1$ vectors on the left and $k$ on the right; this is a misprint, and the item states the correct $[g,\dots,H^kg]$ (consistent with (A.23)). Symmetry of $H$ is the paper's standing setting ($H$ is a Hessian). The other relations (A.3), (A.4), (A.6), (A.7) of Theorem A.1 are not part of this item.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), p. 206, Theorem A.1, (A.2) and (A.5), at ε = 0 as used in the proof of Theorem 2.4, p. 211

import Mathlib
import Definitions.Def_TruncNewton_NegCurv_Setting

namespace TruncNewton.NegCurv

theorem theorem_A_1_eps_zero {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hcurv : ∀ i ≤ k, 0 < inner ℝ ((cg H g i).d) (H (cg H g i).d)) :
    (∀ i j, i ≤ k → j ≤ k → i ≠ j → inner ℝ ((cg H g i).d) (H (cg H g j).d) = 0) ∧
    Submodule.span ℝ ((fun i => (cg H g i).d) '' Set.Iic k) =
      Submodule.span ℝ ((fun i => (H ^ i) g) '' Set.Iic k) := by sorry

end TruncNewton.NegCurv
