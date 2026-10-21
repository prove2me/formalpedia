-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_reflectionStability
-- name    : QAlgorithms.Papers.Independent.Renew46.P12.reflectionStability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:11:55.331315+00:00
-- url     : https://prove2.me/theorems/aa5b55ba-c2a4-4d6d-9d6c-676f8e9701c9
-- title:
--   Frobenius stability of normalized reflections
-- statement:
--   Let $n\ge0$ and let $|\psi\rangle$ and $|\phi\rangle$ be normalized vectors on the same $n$-qubit register. For the reflections $R_v=I-2|v\rangle\langle v|$,
--
--   $$
--   \|R_\psi-R_\phi\|_{\mathrm{Fr}}\le2\sqrt2\,\||\psi\rangle-|\phi\rangle\|_2.
--   $$
--
--   The matrix norm is the ordinary, unnormalized Frobenius norm and the vector norm is Euclidean. This controls the effect of vector approximation on the associated reflections.
-- source:
--   Synthesis of unitaries with Clifford+T circuits, arXiv:1306.3200v1, PDF p. 2, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12

namespace QAlgorithms.Papers.Independent.Renew46.P12

noncomputable section

/-- Proposition 1, PDF p.2: ordinary Frobenius distance is bounded by 2 sqrt(2)
times Euclidean vector distance, with both vectors normalized. Includes n=0. -/
theorem reflectionStability (n : ℕ) (psi phi : EuclideanSpace ℂ (Qubits n))
    (hpsi : IsState psi) (hphi : IsState phi) :
    frobNorm (householderReflection psi - householderReflection phi) ≤ 2 * Real.sqrt 2 * ‖psi - phi‖ := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P12
