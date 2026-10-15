-- Prove2me | Theorems.Thm_QReversal_PGMBound_eq_38
-- name    : QReversal.PGMBound.eq_38
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:21.475478+00:00
-- url     : https://prove2.me/theorems/c1b83926-51e2-48d5-9753-70c5a3176238
-- title:
--   Equation (38): diagonal and off-diagonal trace sums
-- statement:
--   Write $\rho_j=p_j\hat\rho_j$ and $\rho_{\mathrm{out}}=\sum_j\rho_j$. For the classicizing channel and its reversal, with full-support output,
--   $$
--   F_{\mathrm{cl}}(\rho,R_{A,\rho}A)
--   =\sum_j\operatorname{tr}(\rho_{\mathrm{out}}^{-1/2}\rho_j\rho_{\mathrm{out}}^{-1/2}\rho_j)
--   =1-\sum_{i\ne j}\operatorname{tr}(\rho_{\mathrm{out}}^{-1/2}\rho_i\rho_{\mathrm{out}}^{-1/2}\rho_j).
--   $$
--   The second form expresses recovery failure as overlap between distinct ensemble members.
--
--   **Formalization Note** Only the second and third lines of (38) are asserted. The first line involving the squared optimum conflicts with Corollary 4.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 11, (38), second and third lines

import Mathlib
import Definitions.Def_QReversal_PGMBound_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.PGMBound

theorem eq_38 {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) =
      ∑ j, (Matrix.trace
        (QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j *
         QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j)).re ∧
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) =
      1 - ∑ i, ∑ j, if i = j then 0 else
        (Matrix.trace
          (QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v i *
           QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j)).re := by sorry

end QReversal.PGMBound
