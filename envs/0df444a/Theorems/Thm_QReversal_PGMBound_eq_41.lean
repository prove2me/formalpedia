-- Prove2me | Theorems.Thm_QReversal_PGMBound_eq_41
-- name    : QReversal.PGMBound.eq_41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:25.339758+00:00
-- url     : https://prove2.me/theorems/c589dbc1-80db-47d3-b7dd-24506df248ce
-- title:
--   Equation (41): classical fidelity is diagonal-block mass
-- statement:
--   Partition the recovery array $RA$ into $O\times O$ blocks by input label. Then
--   $$
--   F_{\mathrm{cl}}(\rho,R_{A,\rho}A)
--     =\sum_j\sum_{i,i'}|(RA)_{(j,i),(j,i')}|^2.
--   $$
--   The classical fidelity is exactly the squared Frobenius mass of the diagonal blocks.
--
--   **Formalization Note** The right side expands the paper's $\sum_j|(RA)_{jj}|_2^2$ entry by entry.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 12, (41)

import Mathlib
import Definitions.Def_QReversal_PGMBound_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.PGMBound

theorem eq_41 {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) =
      ∑ j, ∑ i, ∑ i',
        Complex.normSq ((Rmat p lam v * Amat p lam v) (j, i) (j, i')) := by sorry

end QReversal.PGMBound
