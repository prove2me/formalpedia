-- Prove2me | Theorems.Thm_WhittEfficiency_IS_sec_2_5_split
-- name    : WhittEfficiency.IS.sec_2_5_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:16.309282+00:00
-- url     : https://prove2.me/theorems/b3635028-c50d-4d1d-88e8-7c15a0c5ef9c
-- title:
--   §2.5, p. 713 — splitting: the class-i arrivals are independent Poisson streams of rates λpᵢ
-- statement:
--   Let arrivals form a Poisson process of rate $\lambda > 0$ and let each customer independently carry a class label $J_k \in \{1,\dots,m\}$ with $P(J_k = i) = p_i$, the labels being independent of the arrival process. For each class $i$ fix a window $(a_i, b_i]$ with $0 \le a_i \le b_i$ (windows of different classes may overlap), and let $A_i(a_i, b_i]$ be the number of class-$i$ arrivals in it. Then
--
--   1. the counts $A_1(a_1,b_1], \dots, A_m(a_m,b_m]$ are mutually independent, and
--   2. each $A_i(a_i,b_i]$ is Poisson with mean $\lambda p_i (b_i - a_i)$:
--   $$P\big(A_i(a_i,b_i] = k\big) = e^{-\lambda p_i (b_i - a_i)}\,\frac{(\lambda p_i (b_i - a_i))^k}{k!}, \qquad k = 0, 1, 2, \dots$$
--
--   This is the content of the paper's observation that, since the arrival process is Poisson, the model is equivalent to the superposition of $m$ independent Poisson arrival processes, the $i$-th with rate $\lambda p_i$.
--
--   **Formalization Note** The page asserts that the class streams are independent Poisson processes; the Lean statement gives the consequence for one window per class, which is the form the next step of the argument uses (windows $(t - d_i, t]$).
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), p. 713, §2.5, fourth sentence

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittEfficiency.IS

/-- Whitt 1992, §2.5, p. 713 (the superposition sentence): with Poisson arrivals of rate `lam`
and i.i.d. class labels with law `p`, the class-`i` arrivals form independent Poisson streams of
rates `lam * p i`. Stated for one window `(a i, b i]` per class (windows of different classes may
overlap): the class window counts are mutually independent and the `i`-th is Poisson with mean
`lam * p i * (b i - a i)`. -/
theorem sec_2_5_split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    {m : ℕ} (p : Fin m → ℝ) (J : ℕ → Ω → Fin m)
    (hM : IsMarkedPoisson μ lam T p J)
    (a b : Fin m → ℝ) (hab : ∀ i, 0 ≤ a i ∧ a i ≤ b i) :
    iIndepFun (fun i ω => classWindowCount T J i (a i) (b i) ω) μ ∧
    ∀ (i : Fin m) (k : ℕ), μ.real {ω | classWindowCount T J i (a i) (b i) ω = k} =
      Real.exp (-(lam * p i * (b i - a i))) * (lam * p i * (b i - a i)) ^ k / k.factorial := by sorry

end WhittEfficiency.IS
