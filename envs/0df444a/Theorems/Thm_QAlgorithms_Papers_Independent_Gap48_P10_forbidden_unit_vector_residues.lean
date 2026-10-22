-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_forbidden_unit_vector_residues
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.forbidden_unit_vector_residues
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:28:29.030668+00:00
-- url     : https://prove2.me/theorems/1d846b3d-2c29-4645-bb0c-50d655dccca5
-- title:
--   Lemma 7.7: forbidden unit-vector residues
-- statement:
--   Let $k\ge2$ be natural and $u,t\in\mathbb Z[\omega]$. Suppose both coefficient residues modulo two belong to $\{0001,0010,0100,1000\}$. Then the vector $v=(u,t)^T/(\sqrt2)^k$ is not a unit vector:
--
--   $$
--   \left|\frac{u}{(\sqrt2)^k}\right|^2+
--   \left|\frac{t}{(\sqrt2)^k}\right|^2\ne1.
--   $$
--   Residues use descending omega-power order. The guard $k\ge2$ is essential: at $k=1$, $u=t=1$ gives a unit vector.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 9, Lemma 7.7: forbidden unit-vector residues

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Lemma 7.7, PDF p.9. The vector is divided by sqrt(2)^k; k>=2 is essential.
Non-unit norm is expressed as the sum of its two actual squared amplitudes. -/
theorem forbidden_unit_vector_residues (k : ℕ) (hk : 2 ≤ k)
    (u t : ℂ) (hu : InZomega u) (ht : InZomega t)
    (hru : residue u = bits 1 ∨ residue u = bits 2 ∨ residue u = bits 4 ∨ residue u = bits 8)
    (hrt : residue t = bits 1 ∨ residue t = bits 2 ∨ residue t = bits 4 ∨ residue t = bits 8) :
    Complex.normSq (u / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) +
      Complex.normSq (t / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) ≠ 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
