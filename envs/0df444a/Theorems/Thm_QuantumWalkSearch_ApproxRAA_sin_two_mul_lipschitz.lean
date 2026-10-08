-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_sin_two_mul_lipschitz
-- name    : QuantumWalkSearch.ApproxRAA.sin_two_mul_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:40:46.322563+00:00
-- url     : https://prove2.me/theorems/d4deba80-4ffb-4496-b6d6-befd9c976b72
-- title:
--   §4, p. 14 — |sin 2A − sin 2B| ≤ 2|sin A − sin B| for A, B ∈ [0, π/4]
-- statement:
--   For all angles $A,B\in[0,\pi/4]$,
--   $$
--   |\sin 2A-\sin 2B|\le 2\,|\sin A-\sin B| .
--   $$
--
--   In the error analysis of Lemma 1 this converts an error on the marked amplitude $\sin\phi_i$ into an error on $\sin2\phi_i$, the factor in front of $\beta_{i+1}$ in the one-level bound.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 14, §4, first trigonometric inequality after Eq. (4)

import Mathlib

namespace QuantumWalkSearch.ApproxRAA

/-- §4, p. 14: `|sin 2A − sin 2B| ≤ 2 |sin A − sin B|` for all angles `A, B ∈ [0, π/4]`. -/
theorem sin_two_mul_lipschitz (A B : ℝ) (hA : A ∈ Set.Icc 0 (Real.pi / 4))
    (hB : B ∈ Set.Icc 0 (Real.pi / 4)) :
    |Real.sin (2 * A) - Real.sin (2 * B)| ≤ 2 * |Real.sin A - Real.sin B| := by sorry

end QuantumWalkSearch.ApproxRAA
