-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_theorem_5_8
-- name    : SingleSampleCombPI.XOS.Supplement.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:51:06.886208+00:00
-- url     : https://prove2.me/theorems/499aff6d-ee18-48e3-81c8-e76ec35aefd5
-- title:
--   Theorem 5.8 (corrected: supremal benchmark) — Full finite-M and limiting concave guarantees
-- statement:
--   For every $M\ge1$, Algorithm 9 is feasible and, for $n$ buyers in every GoG experiment and every fixed real order, has guarantee
--   $$\mathbb E[\mathrm{Alg}_M]\ge c\frac{M}{M+n}\mathbb E[\mathrm{Opt}(r)],\qquad c=\frac{1-e^{-1}}2.$$
--   Consequently, for every fixed $n$ and every $\epsilon>0$, a uniform threshold $M_0\ge1$ works for all $M\ge M_0$, valuation pairs and orders to give ratio at least $c-\epsilon$. This is a limiting lower guarantee; it does not assert that a finite grid attains $c$ or that the actual worst-case ratios converge to equality.
--
--   Differences from the source:
--   - correction: an attained divisible optimum in the benchmark and rounding proof → supremal continuous benchmark, with the unchanged finite-grid maximum; reason: v₁(0)=0, v₁(x)=1 for x>0 and v₂(x)=x are admissible; their welfare supremum is 2 but no feasible allocation attains it; rounding arbitrary feasible allocations and taking suprema retains the full inequality
--   - reading: the competitive ratio approaches (1−1/e)/2 → a lower guarantee approaching c=(1−exp(−1))/2 for fixed n, uniformly over pairs and orders; reason: the proof establishes lower bounds, as also stated by the c−ε guarantee in Table 1; it does not establish equality of exact worst-case ratios
--   - generalization: the theorem sentence gives the asymptotic guarantee → the proof’s explicit finite-M c M/(M+n) bound as well as the full asymptotic guarantee; reason: the finite estimate follows from the proof and Lemma 5.9 and implies the complete source asymptotic statement
--   - encoding: arbitrary normalized monotone concave scalar valuations → native scalar policies and the full feasible/grid benchmarks; reason: no supporting-price oracle, differentiability or continuity at zero is added; real functions are evaluated only on [0,1]
--   - encoding: expectations over the specified independent random choices → explicit fair finite GoG averages and nonnegative expectations over independent algorithm seeds; reason: these are ordinary expectations for measurable source payoffs; no input distribution or finite-support restriction is imposed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 5.8, printed p. 32 / PDF p. 34; proof printed 32, 43 / PDF 34, 45.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Scalar

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Theorem 5.8, PDF 34 / printed 32. Full finite-M guarantee from the
proof and its fixed-n asymptotic consequence, without continuity at zero. -/
theorem theorem_5_8 :
    (∀ n M : ℕ, 1 ≤ M → (alg9 n M).Valid ∧
      ∀ (V : Fin n → Fin 2 → Scalar), (∀ i t, ScalarValid (V i t)) →
        ∀ ρ : Equiv.Perm (Fin n),
        ENNReal.ofReal (concaveRatio * (M:ℝ)/(M+n)) * scalarOptExp V ≤
          scalarExp (alg9 n M) V ρ) ∧
    ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, 1 ≤ M₀ ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ V : Fin n → Fin 2 → Scalar,
        (∀ i t, ScalarValid (V i t)) → ∀ ρ : Equiv.Perm (Fin n),
        ENNReal.ofReal (concaveRatio - ε) * scalarOptExp V ≤
          scalarExp (alg9 n M) V ρ := by sorry

end SingleSampleCombPI.XOS.Supplement
