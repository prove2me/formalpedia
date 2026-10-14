-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_sqrtA_diag
-- name    : QAlgorithms.Arunachalam.sqrtA_diag
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:56:13.815793+00:00
-- url     : https://prove2.me/theorems/f3713153-7752-4922-a7f7-d993f5c6c005
-- title:
--   Diagonal of √A in terms of Fourier coefficients of f
-- statement:
--   Work in the setting of Theorem 7.5.1: let $m\ge10$, $\beta\in(0,1]$ and let $T$ be an integer with $1\le T\le m/(e^3\beta)$; let $f:\{0,1\}^m\to\mathbb R$, $f(z)=(1-\beta|z|/m)^T$, where $|z|$ is the Hamming weight; let $k\le m$ and let $M\in\mathbb F_2^{m\times k}$ have rank $k$; and let $A\in\mathbb R^{2^k\times 2^k}$ be $A(x,y)=(f\circ M)(x+y)=f(M(x+y))$. Then for every $x\in\{0,1\}^k$,
--
--   $$
--   \sqrt A\,(x,x)=\frac1{2^{k/2}}\sum_{Q\in\{0,1\}^k}\sqrt{\sum_{S\in\{0,1\}^m:\,M^{\mathsf T}S=Q}\hat f(S)},
--   $$
--
--   where $\sqrt A$ is the positive semidefinite square root of $A$ and $\hat f$ is the Fourier transform of $f$.
--
--   This expresses the diagonal of $\sqrt A$, which governs the pretty good measurement success probability, through the Fourier coefficients of $f$.
--
--   **Formalization Note** $\sqrt A$ is computed by the continuous functional calculus applied to the symmetric matrix $A$ (the square root of each eigenvalue). The hypotheses of Theorem 7.5.1 are carried as hypotheses of the claim.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 171, Claim 7.5.3. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning




/-- Arunachalam p.170–172, Claim 7.5.3, in the setting of Theorem 7.5.1: `m ≥ 10`,
`f(z) = (1 − β|z|/m)^T` on `{0,1}^m` with `β ∈ (0, 1]` and `T ∈ [1, m/(e³β)]` (a natural number),
`k ≤ m`, `M ∈ F₂^{m×k}` of rank `k`, and `A(x, y) = (f ∘ M)(x + y)` for `x, y ∈ {0,1}^k`. Then for
all `x ∈ {0,1}^k`,
`√A(x, x) = 2^{−k/2} ∑_{Q ∈ {0,1}^k} √(∑_{S ∈ {0,1}^m : Mᵀ S = Q} f̂(S))`,
where `√A` is the positive semidefinite square root of `A`. -/
theorem sqrtA_diag {m k T : ℕ} {β : ℝ} (hm : 10 ≤ m) (hβ : 0 < β) (hβ1 : β ≤ 1) (hT : 1 ≤ T)
    (hTm : (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β)) (hk : k ≤ m)
    (M : Matrix (Fin m) (Fin k) (ZMod 2)) (hM : M.rank = k) (x : Fin k → ZMod 2) :
    psdSqrt (xorConvMatrix fun z => weightPowFun m β T (M.mulVec z)) x x =
      (Real.sqrt ((2 : ℝ) ^ k))⁻¹ *
        ∑ Q : Fin k → ZMod 2, Real.sqrt
          (∑ S ∈ Finset.univ.filter (fun S : Fin m → ZMod 2 => M.transpose.mulVec S = Q),
            boolFourier (weightPowFun m β T) S) := by
  sorry



end QAlgorithms.Arunachalam
