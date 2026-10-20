-- Prove2me | Theorems.Thm_QReversal_PGMBound_eq_36
-- name    : QReversal.PGMBound.eq_36
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:14.49572+00:00
-- url     : https://prove2.me/theorems/dd3b25a2-85db-4a39-916e-980bc299090f
-- title:
--   Equation (36): reversal operators for the classicizing channel
-- statement:
--   For a spectral ensemble $(p_j,\hat\rho_j)$, let $A_{ij}=\sqrt{\lambda_{ij}}|v_{ij}\rangle\langle j|$, $\rho=\sum_jp_j|j\rangle\langle j|$, and $\rho_j=p_j\hat\rho_j$. If $A(\rho)$ has full support, then
--   $$
--   \rho_{\mathrm{out}}=A(\rho)=\sum_j\rho_j,\qquad
--   (R_{A,\rho})_{ij}=\sqrt{p_j\lambda_{ij}}\,|j\rangle\langle v_{ij}|\,\rho_{\mathrm{out}}^{-1/2}.
--   $$
--   This identifies the general reversal operation with the operators of the pretty good measurement.
--
--   **Formalization Note** The inverse is the paper's generalized inverse; full support is the standing assumption accompanying (12).
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 10, (35)–(36)

import Mathlib
import Definitions.Def_QReversal_PGMBound_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.PGMBound

theorem eq_36 {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    rhoOut p lam v = ∑ j, weightedState p lam v j ∧
    ∀ i j, reversal (classicKraus lam v) (rho p) (i, j) =
      ((Real.sqrt (p j) * Real.sqrt (lam i j) : ℂ) •
        vecMulVec (Pi.single j 1) (star (v i j))) *
        QReversal.NearOpt.invSqrt (∑ k, weightedState p lam v k) := by sorry

end QReversal.PGMBound
