-- Prove2me | Theorems.Thm_SelfSelReg_proposition_6_8
-- name    : SelfSelReg.proposition_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:43.674739+00:00
-- url     : https://prove2.me/theorems/069400f5-793d-4927-9566-8b7ae2a401a3
-- title:
--   Proposition 6.8 — largest-gap eigenvalue bounds $\hat\lambda_{i^\star}\ge\|\Lambda\|_{\mathrm{op}}/(2q)$
-- statement:
--   Let $1\le p\le q$, let $W\in\mathbb R^{p\times q}$, and let $\Lambda\in\mathbb R^{q\times q}$ be nonzero and positive semidefinite. Suppose the symmetric matrix $A\in\mathbb R^{p\times p}$ satisfies
--   $$\|A-WW^\top\|_{\mathrm{op}}\le\frac{\|\Lambda\|_{\mathrm{op}}}{8q},\qquad\|W^\top W-\Lambda\|_{\mathrm{op}}\le\frac{\|\Lambda\|_{\mathrm{op}}}{8q}.$$
--   Write eigenvalues in nonincreasing order, put $\hat\lambda_h=\max\{\lambda_h(A),0\}$ for $h\in[p]$, $\hat\lambda_{p+1}=0$ and $\lambda_{q+1}(\Lambda)=0$. Then for every index $i^\star\in\arg\max_{1\le h\le p}(\hat\lambda_h-\hat\lambda_{h+1})$ of a largest eigengap,
--   $$\hat\lambda_{i^\star}\ge\frac{\|\Lambda\|_{\mathrm{op}}}{2q},\qquad\hat\lambda_{i^\star}-\lambda_{i^\star+1}(\Lambda)\ge\frac{\|\Lambda\|_{\mathrm{op}}}{2q}.$$
--
--   Truncating at the largest eigengap therefore keeps eigenvalues bounded away from zero and separated from the rest of the spectrum of $\Lambda$; this makes the rescaling step of the observable-operator construction (Algorithm 6.2) well conditioned.
--
--   **Formalization Note** $\|\cdot\|_{\mathrm{op}}$ is the $\ell^2$ operator norm; $\lambda_h$ is `eigDesc` (nonincreasing, zero beyond the size of the matrix).
--
--   Differences from the source:
--   - reading: for the largest eigengap indexed by i⋆ ∈ arg max_{1≤h≤p}(λ̂_h − λ̂_{h+1}) → for every maximizer i⋆; reason: the non-weaker reading; the conclusion is required of whichever maximizer the algorithm selects
--   - encoding: eigenvalues in nonincreasing order with λ̂_{p+1} = 0, λ_{q+1}(Λ) = 0; a symmetric A → eigDesc (Mathlib's antitone eigenvalues₀, 0 beyond the size), A.IsHermitian over ℝ; reason: same values
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Proposition 6.8, p.39 (PDF p.42); proof Appendix D.2

import Mathlib
import Definitions.Def_SelfSelReg_eigDesc

open scoped Matrix.Norms.L2Operator

namespace SelfSelReg

/-- **Proposition 6.8** (Largest-Gap Eigenvalue Bounds).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Proposition 6.8, p.39 (PDF p.42): "Let 1 ≤ p ≤ q, let W ∈ ℝ^{p×q}, and
let Λ ∈ ℝ^{q×q} be nonzero and positive semidefinite. Suppose the symmetric matrix A ∈ ℝ^{p×p}
satisfies ‖A − WWᵀ‖_op ≤ ‖Λ‖_op/(8q), ‖WᵀW − Λ‖_op ≤ ‖Λ‖_op/(8q). Write the eigenvalues in
nonincreasing order and put λ̂_h = max{λ_h(A), 0}, h ∈ [p], where we understand λ̂_{p+1} = 0 and
λ_{q+1}(Λ) = 0. Then for the largest eigengap indexed by i⋆ ∈ arg max_{1≤h≤p}(λ̂_h − λ̂_{h+1}), we have
λ̂_{i⋆} ≥ ‖Λ‖_op/(2q), λ̂_{i⋆} − λ_{i⋆+1}(Λ) ≥ ‖Λ‖_op/(2q)."

**Formalization Note.** `‖·‖` is the ℓ²-operator norm (`Matrix.Norms.L2Operator`). `λ_h(M)` is
`eigDesc hM h` (nonincreasing, from `h = 1`, and `0` for `h > m`), so `λ̂_h = max (eigDesc hA h) 0`,
`λ̂_{p+1} = 0` and `λ_{q+1}(Λ) = 0` as on the page. "`i⋆ ∈ arg max`" is read for **every** maximizer. -/
theorem proposition_6_8 (p q : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) (W : Matrix (Fin p) (Fin q) ℝ)
    (Λ : Matrix (Fin q) (Fin q) ℝ) (hΛ0 : Λ ≠ 0) (hΛ : Λ.PosSemidef)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsHermitian)
    (h1 : ‖A - W * W.transpose‖ ≤ ‖Λ‖ / (8 * q))
    (h2 : ‖W.transpose * W - Λ‖ ≤ ‖Λ‖ / (8 * q)) (istar : ℕ) (hi1 : 1 ≤ istar) (hip : istar ≤ p)
    (hmax : ∀ h : ℕ, 1 ≤ h → h ≤ p →
      max (eigDesc hA h) 0 - max (eigDesc hA (h + 1)) 0 ≤
        max (eigDesc hA istar) 0 - max (eigDesc hA (istar + 1)) 0) :
    ‖Λ‖ / (2 * q) ≤ max (eigDesc hA istar) 0 ∧
      ‖Λ‖ / (2 * q) ≤ max (eigDesc hA istar) 0 - eigDesc hΛ.isHermitian (istar + 1) := by sorry

end SelfSelReg
