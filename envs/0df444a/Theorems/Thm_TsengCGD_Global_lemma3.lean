-- Prove2me | Theorems.Thm_TsengCGD_Global_lemma3
-- name    : TsengCGD.Global.lemma3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:49.673507+00:00
-- url     : https://prove2.me/theorems/0b1fd052-fdc8-485b-a17b-ef33d45d6818
-- title:
--   Lemma 3 — comparison of directions under two quadratic matrices
-- statement:
--   Let $x\in\operatorname{dom}P$, let $\mathcal J$ be nonempty, and let $H,\widetilde H$ be positive definite. Set $d=d_H(x;\mathcal J)$, $\widetilde d=d_{\widetilde H}(x;\mathcal J)$, and $Q=H_{\mathcal J\mathcal J}^{-1/2}\widetilde H_{\mathcal J\mathcal J}H_{\mathcal J\mathcal J}^{-1/2}$. Lemma 3 bounds the change of direction by
--
--   $$\|\widetilde d\|\le
--   \frac{1+\lambda_{\max}(Q)+\sqrt{1-2\lambda_{\min}(Q)+\lambda_{\max}(Q)^2}}{2}
--   \frac{\lambda_{\max}(H_{\mathcal J\mathcal J})}{\lambda_{\min}(\widetilde H_{\mathcal J\mathcal J})}\|d\|.$$
--
--   If $H_{\mathcal J\mathcal J}\succ\widetilde H_{\mathcal J\mathcal J}$, the second conclusion is
--
--   $$\|d\|\le\sqrt{\frac{\lambda_{\max}(H_{\mathcal J\mathcal J}-\widetilde H_{\mathcal J\mathcal J})}{\lambda_{\min}(H_{\mathcal J\mathcal J}-\widetilde H_{\mathcal J\mathcal J})}}\|\widetilde d\|.$$
--
--   Together these estimates control the direction when the quadratic model changes.
--
--   **Formalization Note** The extreme eigenvalues are represented by Rayleigh quotient extrema on vectors supported in $\mathcal J$. Generalized quotients represent $Q$'s spectrum. The nonempty block and positive-definite matrices make their defining sets nonempty and bounded; the square-root arguments are nonnegative.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 394, Lemma 3, equations (18)–(19), https://doi.org/10.1007/s10107-007-0170-0

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem lemma3 {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (H Ht : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (hHt : Ht.PosDef) :
    let d := dH f D P c H x J
    let dt := dH f D P c Ht x J
    ‖dt‖ ≤
      ((1 + genMax H Ht J +
        Real.sqrt (1 - 2 * genMin H Ht J + (genMax H Ht J) ^ 2)) / 2) *
        (lamMax H J / lamMin Ht J) * ‖d‖ ∧
    ((∀ u : Vec n, SupportedOn J u → u ≠ 0 → qf Ht u < qf H u) →
      ‖d‖ ≤ Real.sqrt (lamMax (H - Ht) J / lamMin (H - Ht) J) * ‖dt‖) := by sorry

end TsengCGD.Global
