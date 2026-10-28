-- Prove2me | Theorems.Thm_QReversal_PGMBound_eq_42
-- name    : QReversal.PGMBound.eq_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:33.032055+00:00
-- url     : https://prove2.me/theorems/451afee5-2adf-4310-9474-fb6bd70ded6a
-- title:
--   Equation (42): trace norm of an off-diagonal Gram block
-- statement:
--   Let $B=A^\dagger A$, and let $B_{kl}$ be its block from label $l$ to label $k$. Then
--   $$
--   |B_{kl}|_1=\sqrt{p_kp_l}\,F_{\mathrm{BU}}(\hat\rho_k,\hat\rho_l).
--   $$
--   This identifies the weighted pairwise overlap used in Theorem 5.
--
--   **Formalization Note** The printed calculation obtains the fidelity with arguments reversed; symmetry gives the displayed order. The trace norm is the published WildeQIT.traceNorm.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 12, (42) and sentence following

import Mathlib
import Definitions.Def_QReversal_PGMBound_Setting
import Definitions.Def_WildeQIT_traceNorm

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.PGMBound

theorem eq_42 {J : Type*} {O : Type} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) (k l : J) :
    WildeQIT.traceNorm (Bblk p lam v k l) =
      Real.sqrt (p k * p l) * FBU (rhoHat lam v k) (rhoHat lam v l) := by sorry

end QReversal.PGMBound
