-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_cliffordT_entry_rings
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.cliffordT_entry_rings
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:22:00.247245+00:00
-- url     : https://prove2.me/theorems/59477fbb-8ce6-48fb-98fd-323c33dc84fd
-- title:
--   Remark 4.4: entry rings
-- statement:
--   Let $U$ be an exact single-qubit Clifford+$T$ operator and $\widehat U$ its Bloch matrix in ordered $X,Y,Z$ coordinates. Let $\mathbb D=\mathbb Z[1/2]$ and $\omega=e^{i\pi/4}$. Then
--
--   $$
--   U_{ij}\in\mathbb D[\omega],\qquad
--   \widehat U_{ab}\in\mathbb D[\sqrt2]
--   $$
--   for every respective matrix entry. The first ring consists of dyadic combinations of $\omega^3,\omega^2,\omega,1$; the second is $\mathbb Z[1/\sqrt2]$.
--
--   These are the two separate arithmetic domains used for exact synthesis and denominator counts.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 4, Remark 4.4: entry rings

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Remark 4.4, PDF p.4: both entry-ring conclusions, with the actual Bloch map. -/
theorem cliffordT_entry_rings (U : Mat) (hU : CliffordT U) :
    (∀ i j, InDomega (U i j)) ∧ (∀ i j, InDsqrt2 (operatorBloch U i j)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
