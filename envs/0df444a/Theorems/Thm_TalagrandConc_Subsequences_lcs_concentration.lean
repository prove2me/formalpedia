-- Prove2me | Theorems.Thm_TalagrandConc_Subsequences_lcs_concentration
-- name    : TalagrandConc.Subsequences.lcs_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:05.753429+00:00
-- url     : https://prove2.me/theorems/815d5975-fe93-439a-a252-3748111d2574
-- title:
--   Theorem 7.2.1 — P(L_{N,N'} ≥ M+u) ≤ 2exp(−u²/(32(M+u))), P(L_{N,N'} ≤ M−u) ≤ 2exp(−u²/(32M))
-- statement:
--   Let $X$ be a real random variable with law $\mu$, and let $(X_i)_{i \le N}$, $(Y_j)_{j \le N'}$ be two independent sequences of independent random variables distributed like $X$. Let
--   $$L_{N,N'} = L_{N,N'}(X_1,\dots,X_N;\ Y_1,\dots,Y_{N'})$$
--   be the length of their longest common subsequence, and let $M$ be a median of $L_{N,N'}$. Then for all $u > 0$,
--   $$P(L_{N,N'} \ge M + u) \le 2\exp\Big(-\frac{u^2}{32(M+u)}\Big), \tag{7.2.1}$$
--   $$P(L_{N,N'} \le M - u) \le 2\exp\Big(-\frac{u^2}{32M}\Big). \tag{7.2.2}$$
--
--   When $X$ takes many values the median is much smaller than $N$, and these bounds improve on what Azuma's inequality gives.
--
--   **Formalization Note** The two sequences are the coordinates of $\mathbb R^N \times \mathbb R^{N'}$ under $P = \mu^{\otimes N} \otimes \mu^{\otimes N'}$. When $M = 0$ Lean's division gives $u^2/(32M) = 0$, so (7.2.2) reads $P(L_{N,N'} \le -u) \le 2$; the event is empty, so nothing is lost.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 154, Theorem 7.2.1, Eqs. (7.2.1)–(7.2.2)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.Subsequences

/-- Talagrand (1995), Theorem 7.2.1, p. 154. Let `X` be a real random variable with law `μ`
and `(X_i)_{i ≤ N}`, `(Y_j)_{j ≤ N'}` independent sequences distributed like `X`, realised as
the coordinates of `ℝ^N × ℝ^{N'}` under `P = μ^{⊗N} ⊗ μ^{⊗N'}`. If `M` is a median of
`L_{N,N'} = L_{N,N'}(X_1, …, X_N; Y_1, …, Y_{N'})`, then for all `u > 0`,
(7.2.1) `P(L_{N,N'} ≥ M + u) ≤ 2 exp(−u² / (32(M + u)))` and
(7.2.2) `P(L_{N,N'} ≤ M − u) ≤ 2 exp(−u² / (32M))`. -/
theorem lcs_concentration {N N' : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian ((Measure.pi fun _ : Fin N => μ).prod (Measure.pi fun _ : Fin N' => μ))
      (fun z => (lcs z.1 z.2 : ℝ)) M)
    (u : ℝ) (hu : 0 < u) :
    ((Measure.pi fun _ : Fin N => μ).prod (Measure.pi fun _ : Fin N' => μ))
        {z | M + u ≤ (lcs z.1 z.2 : ℝ)} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (32 * (M + u))))) ∧
      ((Measure.pi fun _ : Fin N => μ).prod (Measure.pi fun _ : Fin N' => μ))
        {z | (lcs z.1 z.2 : ℝ) ≤ M - u} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (32 * M)))) := by sorry

end TalagrandConc.Subsequences
