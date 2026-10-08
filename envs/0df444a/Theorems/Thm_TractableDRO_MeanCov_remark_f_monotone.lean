-- Prove2me | Theorems.Thm_TractableDRO_MeanCov_remark_f_monotone
-- name    : TractableDRO.MeanCov.remark_f_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:20.991421+00:00
-- url     : https://prove2.me/theorems/de215a63-f731-45e4-b466-fb4c382a2a49
-- title:
--   Remark after Theorem 2, p. 910 — f(u) = ½u + ½√(u² + y′Σy) is nondecreasing in u
-- statement:
--   Let $\Sigma \in \mathbb R^{N \times N}$ be a symmetric positive semidefinite matrix and $y \in \mathbb R^{N}$. Then the function
--
--   $$f(u) = \tfrac12 u + \tfrac12 \sqrt{u^2 + y'\Sigma y}, \qquad u \in \mathbb R,$$
--
--   is nondecreasing on all of $\mathbb R$.
--
--   In the paper this observation is what turns the inner supremum over the mean set in (22) into a single linear constraint, giving the conic reformulation (23) of $\pi^2$.
--
--   **Formalization Note** Positive semidefiniteness of $\Sigma$ (a covariance matrix in the paper) makes $y'\Sigma y \ge 0$; it is required, because with a negative constant under the root Lean's `Real.sqrt` returns $0$ for negative arguments and the function is not monotone.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 910, Remark after Theorem 2

import Mathlib
import Definitions.Def_TractableDRO_MeanCov_Model

open Matrix

namespace TractableDRO.MeanCov

theorem remark_f_monotone {N : ℕ} (Sig : Matrix (Fin N) (Fin N) ℝ) (hSig : Sig.PosSemidef)
    (y : Fin N → ℝ) :
    Monotone (fun u : ℝ => u / 2 + Real.sqrt (u ^ 2 + y ⬝ᵥ Sig *ᵥ y) / 2) := by sorry

end TractableDRO.MeanCov
