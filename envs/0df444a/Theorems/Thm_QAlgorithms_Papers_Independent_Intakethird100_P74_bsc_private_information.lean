-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P74_bsc_private_information
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P74.bsc_private_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:11:04.572204+00:00
-- url     : https://prove2.me/theorems/10543173-9fa2-475c-bc5f-3e93e13a94f2
-- title:
--   Symmetric private information of independent binary symmetric channels
-- statement:
--   Let $p_B,p_E\in[0,1]$. Conditioned on a uniform binary input $x$, Bob and Eve receive independent BSC outputs, with transition law $p(y,z\mid x)=p_B(y\mid x)p_E(z\mid x)$, where each factor equals $1-p$ for an unchanged bit and $p$ for a flipped bit. Let $W_B,W_E$ be their diagonal quantum output ensembles and let $H_2$ denote binary entropy in bits. Then
--
--   $$
--   I(W_B)-I(W_E)=H_2(p_E)-H_2(p_B).
--   $$
--
--   Under the additional flip convention $p_B,p_E\le1/2$,
--
--   $$
--   I(W_B)-I(W_E)>0\quad\Longleftrightarrow\quad p_B<p_E.
--   $$
--
--   The entropy identity applies on the full probability square; the positivity equivalence uses the parameter convention visible in the source's figure.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, PDF p. 7, Appendix C.A, unnumbered: symmetric private information of independent BSC wiretap channel

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {B E S1 S2 : Type}

variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]

variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF p.7, Appendix C.A: exact entropy identity on [0,1]^2; the stated positivity
criterion uses the [0,1/2]^2 flip convention of Fig.1. -/
theorem bsc_private_information (pB pE : ℝ)
    (hB0 : 0 ≤ pB) (hB1 : pB ≤ 1) (hE0 : 0 ≤ pE) (hE1 : pE ≤ 1) :
    uniformHolevo (bscOutput pB) - uniformHolevo (bscOutput pE) =
      binEntropy2 pE - binEntropy2 pB ∧
    (pB ≤ 1 / 2 → pE ≤ 1 / 2 →
      (0 < uniformHolevo (bscOutput pB) - uniformHolevo (bscOutput pE) ↔ pB < pE)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P74
