-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_theorem1
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.theorem1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:43:20.255609+00:00
-- url     : https://prove2.me/theorems/c55a7b2e-881e-4d82-bfc3-c57ba639d351
-- title:
--   Theorem 1: dual universality bound
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. Suppose $\varepsilon\ge0$ and the family satisfies its minimum-dimension universality bound. Put $t=t_{\min}$ and $\varepsilon'=2(1-2^{t-n}\varepsilon)+(\varepsilon-1)2^t$. Then the dual family has maximum dimension $n-t$, is $\varepsilon'$-almost universal at that maximum dimension, and
--
--   $$\forall x\ne0,\quad\Pr_r[x\in C_r^\perp]\le(1-2^{t-n}\varepsilon)2^{1-t}+\varepsilon-1.$$
--
--   This relates ordinary and dual universality, retaining the distinction between the two dimension conventions.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 4, Theorem 1: dual universality bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.4--5, Theorem 1 and (8). Negative exponents are real exponents. -/
theorem theorem1 {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (C : I → BinaryLinearCode n) (eps : ℝ) (heps : 0 ≤ eps)
    (hC : UniversalAt C (minDim C) eps) :
    maxDim (fun r => binDual (C r)) = n - minDim C ∧
    UniversalAt (fun r => binDual (C r)) (n - minDim C) (dualParameter n (minDim C) eps) ∧
    ∀ x : BinaryBlock n, x ≠ 0 → seedProbability (fun r => x ∈ binDual (C r)) ≤
      (1 - (2 : ℝ) ^ ((minDim C : ℝ) - n) * eps) *
        (2 : ℝ) ^ (1 - (minDim C : ℝ)) + eps - 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
