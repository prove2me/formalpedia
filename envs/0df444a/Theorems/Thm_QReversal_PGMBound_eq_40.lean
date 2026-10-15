-- Prove2me | Theorems.Thm_QReversal_PGMBound_eq_40
-- name    : QReversal.PGMBound.eq_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:22.062865+00:00
-- url     : https://prove2.me/theorems/e67bba1b-431a-40b1-aaa0-ccf756268bd9
-- title:
--   Equation (40): unit squared Frobenius norm
-- statement:
--   For the recovery array $RA$ of a normalized spectral ensemble with full-support output,
--   $$
--   |RA|_2^2=\sum_{a,b}|(RA)_{ab}|^2=1.
--   $$
--   This is the total mass partitioned into diagonal and off-diagonal blocks.
--
--   **Formalization Note** Both array indices range over $J\times O$, and each term is the squared complex modulus.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 12, (40)

import Mathlib
import Definitions.Def_QReversal_PGMBound_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.PGMBound

theorem eq_40 {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    ∑ a : J × O, ∑ b : J × O,
      Complex.normSq ((Rmat p lam v * Amat p lam v) a b) = 1 := by sorry

end QReversal.PGMBound
