-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_sin_three_mul_lipschitz
-- name    : QuantumWalkSearch.ApproxRAA.sin_three_mul_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:39.04143+00:00
-- url     : https://prove2.me/theorems/8a810f09-c0b7-4da1-a25e-c216237d3a6c
-- title:
--   §4, p. 14 — |sin 3A − sin 3B| ≤ 3|sin A − sin B| for A, B ∈ [0, π/4]
-- statement:
--   For all angles $A,B\in[0,\pi/4]$,
--   $$
--   |\sin 3A-\sin 3B|\le 3\,|\sin A-\sin B| .
--   $$
--
--   In the error analysis of Lemma 1 this shows that one level of amplitude amplification at most triples an error on the marked amplitude.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 14, §4, second trigonometric inequality after Eq. (4)

import Mathlib

namespace QuantumWalkSearch.ApproxRAA

/-- §4, p. 14: `|sin 3A − sin 3B| ≤ 3 |sin A − sin B|` for all angles `A, B ∈ [0, π/4]`. -/
theorem sin_three_mul_lipschitz (A B : ℝ) (hA : A ∈ Set.Icc 0 (Real.pi / 4))
    (hB : B ∈ Set.Icc 0 (Real.pi / 4)) :
    |Real.sin (3 * A) - Real.sin (3 * B)| ≤ 3 * |Real.sin A - Real.sin B| := by sorry

end QuantumWalkSearch.ApproxRAA
