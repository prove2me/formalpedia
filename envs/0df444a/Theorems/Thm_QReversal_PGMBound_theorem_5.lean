-- Prove2me | Theorems.Thm_QReversal_PGMBound_theorem_5
-- name    : QReversal.PGMBound.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:24.471743+00:00
-- url     : https://prove2.me/theorems/c7a3a8dd-f62a-484f-92d8-42443c9eb448
-- title:
--   Theorem 5, proved reading: PGM error bounded by weighted Bures–Uhlmann overlaps
-- statement:
--   Let $(p_j,\hat\rho_j)$ be a finite ensemble of density matrices with spectral decompositions $\hat\rho_j=\sum_i\lambda_{ij}|v_{ij}\rangle\langle v_{ij}|$. Let $A_{ij}=\sqrt{\lambda_{ij}}|v_{ij}\rangle\langle j|$, $\rho=\sum_jp_j|j\rangle\langle j|$, and suppose $A(\rho)$ has full support. Then
--   $$
--   F_{\mathrm{cl}}(\rho,R_{A,\rho}A)
--      \geq 1-\sum_{i\ne j}\sqrt{p_ip_j}\,
--         F_{\mathrm{BU}}(\hat\rho_i,\hat\rho_j).
--   $$
--   The sum is over ordered pairs, counting every distinct unordered pair twice. The result bounds the pretty good measurement's error for mixed-state ensembles.
--
--   **Formalization Note** Equation (39) prints $F_{\mathrm{cl}}^2$, where $F_{\mathrm{cl}}$ means optimal success probability. Its preceding (38) reverses Corollary 4's comparison. Pages 12–13 prove the displayed bound for $F_{\mathrm{cl}}(\rho,R_{A,\rho}A)$, which is the form posed here. The generalized inverse and full-support assumption follow page 7.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, pp. 11–13, Theorem 5 (39), proved reading

import Mathlib
import Definitions.Def_QReversal_PGMBound_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.PGMBound

theorem theorem_5 {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    1 - ∑ i, ∑ j, (if i = j then 0 else
      Real.sqrt (p i * p j) * FBU (rhoHat lam v i) (rhoHat lam v j)) ≤
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) := by sorry

end QReversal.PGMBound
