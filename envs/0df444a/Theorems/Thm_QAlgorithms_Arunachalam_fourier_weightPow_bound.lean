-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_fourier_weightPow_bound
-- name    : QAlgorithms.Arunachalam.fourier_weightPow_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:56:13.560843+00:00
-- url     : https://prove2.me/theorems/b77f3fdd-6a46-4c0c-8045-4db52e0dedce
-- title:
--   Fourier coefficients of (1 − β|z|/m)^T are nonnegative and small
-- statement:
--   Let $m\ge10$, $\beta\in(0,1]$ and let $T$ be an integer with $1\le T\le m/(e^3\beta)$ (the setting of Theorem 7.5.1). Let $f:\{0,1\}^m\to\mathbb R$, $f(z)=(1-\beta|z|/m)^T$, with Fourier coefficients $\hat f(S)=\mathbb E_z[f(z)(-1)^{S\cdot z}]$. Then for every $S\in\{0,1\}^m$ of Hamming weight $|S|=q$,
--
--   $$
--   0\ \le\ \hat f(S)\ \le\ 4e\left(1-\frac\beta2\right)^T\left(\frac{T\beta}{m}\right)^q e^{22T^2\beta^2/m}.
--   $$
--
--   Combined with Claim 7.5.3 this bounds the diagonal of $\sqrt A$ in Theorem 7.5.1.
--
--   **Formalization Note** The conditions $m\ge10$ and $1\le T\le m/(e^3\beta)$ are those of Theorem 7.5.1, which the proof of the lemma uses.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 172, Lemma 7.5.4. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning





/-- Arunachalam p.172–175, Lemma 7.5.4, in the setting of Theorem 7.5.1 (`m ≥ 10`,
`T ∈ [1, m/(e³β)]` a natural number, which the proof uses): for `β ∈ (0, 1]`, the Fourier
coefficients of `f(z) = (1 − β|z|/m)^T` on `{0,1}^m` satisfy
`0 ≤ f̂(S) ≤ 4e (1 − β/2)^T (Tβ/m)^q e^{22T²β²/m}` for all `S` with `|S| = q`. -/
theorem fourier_weightPow_bound {m T : ℕ} {β : ℝ} (hm : 10 ≤ m) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hT : 1 ≤ T) (hTm : (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β)) (S : Fin m → ZMod 2) :
    0 ≤ boolFourier (weightPowFun m β T) S ∧
      boolFourier (weightPowFun m β T) S ≤
        4 * Real.exp 1 * (1 - β / 2) ^ T * ((T : ℝ) * β / (m : ℝ)) ^ hammingNorm S *
          Real.exp (22 * (T : ℝ) ^ 2 * β ^ 2 / (m : ℝ)) := by
  sorry


end QAlgorithms.Arunachalam
