-- Prove2me | Theorems.Thm_RISRO_lemma_2_spectrum_bounds
-- name    : RISRO.lemma_2_spectrum_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:33:40.591847+00:00
-- url     : https://prove2.me/theorems/57d1f48a-f09d-4db9-af7f-fb86f1f84d8b
-- title:
--   Lemma 2 — bounds for the spectrum of $\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t$
-- statement:
--   Let $\mathcal A:\mathbb R^{p_1\times p_2}\to\mathbb R^n$, $\mathcal A(X)_i=\langle A_i,X\rangle$, and $y\in\mathbb R^n$. Let $U,V$ be orthonormal with orthonormal complements $U_\perp,V_\perp$, and let $\mathcal L_t$ be the operator of (9).
--    Then $\|\mathcal L_t(M)\|_F=\|M\|_F$ for every $M\in\mathrm{Ran}(\mathcal L_t^*)$. If moreover $\mathcal A$ satisfies the $2r$-RIP, then for every $M\in\mathrm{Ran}(\mathcal L_t^*)$
--
--   $$
--   (1-R_{2r})\|M\|_F\le\|\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t(M)\|_F\le(1+R_{2r})\|M\|_F .
--   $$
--
--   In particular the least squares problem (5) has a unique solution under the $2r$-RIP.
--
--   Differences from the source:
--   - generalization: the data U^t, V^t, U_⊥^t, V_⊥^t of an iteration of RISRO → any orthonormal frames with orthonormal complements; reason: the proof uses only orthonormality; every iteration of every run supplies such frames
--   - encoding: matrices M ∈ Ran(L_t^*) with a zero bottom-right block → triples (W₀, W₁, W₂) with tripleNorm; reason: the same space with the same norm
--   - generalization: R_k defined for 1 ≤ k ≤ min(p₁, p₂) (Definition 1) → ripConst A k for every k; reason: it agrees with Definition 1 where that is defined; the paper uses R_{3r} and Lemma 8 at rank 3r, which may exceed min(p₁, p₂)
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Lemma 2, display (17), p.10

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_IsFrame
import Definitions.Def_RISRO_Triple
import Definitions.Def_RISRO_tripleNorm
import Definitions.Def_RISRO_Lop
import Definitions.Def_RISRO_normalOp

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Lemma 2 (Bounds for Spectrum of `L_t^* A^* A L_t`).** `‖L_t(M)‖_F = ‖M‖_F` for every
`M ∈ Ran(L_t^*)` (17), and if `A` satisfies the `2r`-RIP then
`(1 - R_{2r})‖M‖_F ≤ ‖L_t^* A^* A L_t(M)‖_F ≤ (1 + R_{2r})‖M‖_F`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Lemma 2, display (17), p.10.

Formalization Notes: `R_k` is `ripConst A k`, defined for every `k`; "`A` satisfies the `2r`-RIP"
is `ripConst A (2 * r) < 1`. `Ran(L_t^*)` is `Triple p₁ p₂ r`. -/
theorem lemma_2_spectrum_bounds {p₁ p₂ n r : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (hU : IsFrame U Uc) (hV : IsFrame V Vc) :
    (∀ W : Triple p₁ p₂ r, frobeniusNorm (Lop U Uc V Vc W) = tripleNorm W) ∧
      (ripConst A (2 * r) < 1 → ∀ W : Triple p₁ p₂ r,
        (1 - ripConst A (2 * r)) * tripleNorm W ≤ tripleNorm (normalOp A U Uc V Vc W) ∧
          tripleNorm (normalOp A U Uc V Vc W) ≤ (1 + ripConst A (2 * r)) * tripleNorm W) := by sorry

end RISRO
