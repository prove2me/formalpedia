-- Prove2me | Theorems.Thm_RFRidge_Basic_proposition_9
-- name    : RFRidge.Basic.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:54.514509+00:00
-- url     : https://prove2.me/theorems/589245aa-a362-4daa-9e0b-97e496a14123
-- title:
--   Proposition 9, Eq. (44), p. 41 — ‖XA^σ‖ ≤ ‖X‖^{1−σ}‖XA‖^σ for positive A and σ ∈ [0, 1]
-- statement:
--   Let $\mathcal H,\mathcal K$ be Hilbert spaces, $X:\mathcal H\to\mathcal K$ a bounded linear operator and $A:\mathcal H\to\mathcal H$ a bounded positive semidefinite operator. Then
--   $$\|XA^\sigma\|\le\|X\|^{1-\sigma}\,\|XA\|^\sigma\qquad\text{for all }\sigma\in[0,1].$$
--
--   This interpolation inequality splits the computational error finely in Lemma 4 and Theorem 4.
--
--   **Formalization Note** The operator $X$ of the page is called `T` in Lean, because `X` names the input space elsewhere in this mission. The spaces are complex Hilbert spaces and $A^\sigma$ is the continuous functional calculus power (see Proposition 4); separability is dropped. Real powers of norms use $0^0=1$, matching $A^0=I$.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Proposition 9, Eq. (44), p. 41

import Mathlib

namespace RFRidge.Basic

/-- Proposition 9, Eq. (44), p. 41: for a bounded operator `T : E → F` between Hilbert spaces (the
paper's `X`) and a positive semidefinite bounded operator `A` on `E`,
`‖T A^σ‖ ≤ ‖T‖^{1−σ} ‖T A‖^σ` for every `σ ∈ [0, 1]`. Posed on complex Hilbert spaces, with `A^σ` the
`CFC.rpow` power. -/
theorem proposition_9 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (A : E →L[ℂ] E) (hA : 0 ≤ A) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖T ∘L A ^ σ‖ ≤ ‖T‖ ^ (1 - σ) * ‖T ∘L A‖ ^ σ := by sorry

end RFRidge.Basic
