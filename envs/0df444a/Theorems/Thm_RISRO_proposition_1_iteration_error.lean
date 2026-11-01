-- Prove2me | Theorems.Thm_RISRO_proposition_1_iteration_error
-- name    : RISRO.proposition_1_iteration_error
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:34:57.543731+00:00
-- url     : https://prove2.me/theorems/a058536a-479c-43ac-beb0-a37955df9caa
-- title:
--   Proposition 1 — upper bound for the iteration approximation error
-- statement:
--   Let $\bar X$ be a rank $r$ target, $\bar\epsilon=y-\mathcal A(\bar X)$, and suppose $\mathcal A$ satisfies the $2r$-RIP. Then at the $t$-th iteration of RISRO, in which $\|\cdot\|$ is the spectral norm,
--
--   $$
--   \bigl\|(\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t)^{-1}\mathcal L_t^*\mathcal A^*\epsilon^t\bigr\|_F^2
--   \le\frac{R_{3r}^2\|X^t-\bar X\|^2\|X^t-\bar X\|_F^2}{(1-R_{2r})^2\sigma_r^2(\bar X)}+\frac{\|\mathcal L_t^*\mathcal A^*(\bar\epsilon)\|_F^2}{(1-R_{2r})^2}+\|\mathcal L_t^*\mathcal A^*(\bar\epsilon)\|_F\frac{2R_{3r}\|X^t-\bar X\|\|X^t-\bar X\|_F}{\sigma_r(\bar X)(1-R_{2r})^2}.
--   $$
--
--   The bound applies to any rank $r$ target, in particular to a stationary point or to a ground-truth matrix.
--
--   Differences from the source:
--   - generalization: the t-th iterate X^t, U^t, V^t of RISRO → any frames U, V with X = U S Vᵀ for some r×r matrix S, rank X not assumed; reason: the proof uses only this form (reading R5); every iterate of every run has it
--   - generalization: R_k defined for 1 ≤ k ≤ min(p₁, p₂) (Definition 1) → ripConst A k for every k; reason: it agrees with Definition 1 where that is defined; the paper uses R_{3r} and Lemma 8 at rank 3r, which may exceed min(p₁, p₂)
--   - encoding: (L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t → the w with normalOp w = L_t^* A^* ϵ^t (IsErrorTriple); reason: the operator is injective here, so w is unique and equals the page's expression
--   - encoding: matrices M ∈ Ran(L_t^*) with a zero bottom-right block → triples (W₀, W₁, W₂) with tripleNorm; reason: the same space with the same norm
--   - encoding: rank r, r implicitly positive → explicit hypothesis 1 ≤ r; reason: σ_r is undefined at r = 0; this excludes only that undefined case
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Proposition 1, display (18), p.11

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_Triple
import Definitions.Def_RISRO_tripleNorm
import Definitions.Def_RISRO_LopAdj
import Definitions.Def_RISRO_IsErrorTriple
import Definitions.Def_RISRO_IsIterate

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Proposition 1 (Upper Bound for Iteration Approximation Error).** Let `X̄` be a rank `r` target,
`ϵ̄ = y - A(X̄)`, and let `A` satisfy the `2r`-RIP. Then at the `t`-th iteration of RISRO,
`‖(L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t‖_F²` is at most
`R_{3r}² ‖X^t - X̄‖² ‖X^t - X̄‖_F² / ((1 - R_{2r})² σ_r²(X̄)) + ‖L_t^* A^*(ϵ̄)‖_F² / (1 - R_{2r})²
 + ‖L_t^* A^*(ϵ̄)‖_F · 2 R_{3r} ‖X^t - X̄‖ ‖X^t - X̄‖_F / (σ_r(X̄) (1 - R_{2r})²)`, which is (18).

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Proposition 1, display (18), p.11.

Formalization Notes: "at the `t`-th iteration" is `IsIterate U Uc V Vc X`, which every iterate of
every run satisfies; `w` is the unique solution of `IsErrorTriple` (unique by Lemma 2). `‖·‖` is the
spectral norm `opNorm`, `‖·‖_F` is `frobeniusNorm`. -/
theorem proposition_1_iteration_error {p₁ p₂ n r : ℕ} (hr : 1 ≤ r) (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (Xbar X : Matrix (Fin p₁) (Fin p₂) ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (hrank : Xbar.rank = r) (hRIP : ripConst A (2 * r) < 1) (hIter : IsIterate U Uc V Vc X)
    (w : Triple p₁ p₂ r) (hw : IsErrorTriple A y Xbar U Uc V Vc w) :
    tripleNorm w ^ 2 ≤
      ripConst A (3 * r) ^ 2 * opNorm (X - Xbar) ^ 2 * frobeniusNorm (X - Xbar) ^ 2 /
          ((1 - ripConst A (2 * r)) ^ 2 * sv Xbar (r - 1) ^ 2) +
        tripleNorm (LopAdj U Uc V Vc (observationOpAdjoint A (y - observationOp A Xbar))) ^ 2 /
          (1 - ripConst A (2 * r)) ^ 2 +
        tripleNorm (LopAdj U Uc V Vc (observationOpAdjoint A (y - observationOp A Xbar))) *
          (2 * ripConst A (3 * r) * opNorm (X - Xbar) * frobeniusNorm (X - Xbar) /
            (sv Xbar (r - 1) * (1 - ripConst A (2 * r)) ^ 2)) := by sorry

end RISRO
