-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_theorem4
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.theorem4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:47:20.736289+00:00
-- url     : https://prove2.me/theorems/df284dda-8e82-4c75-82ab-96ef748746c7
-- title:
--   Theorem 4, bound clause: dual of a universal extended-code family
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. Fix a dimension-$m$ code $B$ and suppose $B\le C_r$ for every seed. Assume $\varepsilon\ge0$ and $\Pr_r[x\in C_r]\le\varepsilon2^{t-n}$ for every $x\notin B$, with $t=t_{\min}$. The duals lie in $B^\perp$, have maximum dimension $n-t$, and are subcode universal with parameter $2(1-2^{t-n}\varepsilon)+(\varepsilon-1)2^{t-m}$. In particular,
--
--   $$\forall x\in B^\perp\setminus\{0\},\quad\Pr_r[x\in C_r^\perp]\le(1-2^{t-n}\varepsilon)2^{1-t+m}+\varepsilon-1.$$
--
--   The sharpness clause is separately deferred.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 6, Theorem 4, bound clause: dual of a universal extended-code family

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.6--7, Theorem 4, bound clause: the dual family consists of subcodes. -/
theorem theorem4 {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (B : BinaryLinearCode n) (C : I → BinaryLinearCode n) (eps : ℝ) (heps : 0 ≤ eps)
    (hu : ExtUniversalAt B C (minDim C) eps) :
    maxDim (fun r => binDual (C r)) = n - minDim C ∧
    SubUniversalAt (binDual B) (fun r => binDual (C r)) (n - minDim C)
      (2 * (1 - (2 : ℝ) ^ ((minDim C : ℝ) - n) * eps) +
        (eps - 1) * (2 : ℝ) ^ ((minDim C : ℝ) - Module.finrank (ZMod 2) B)) ∧
    ∀ x ∈ binDual B, x ≠ 0 → seedProbability (fun r => x ∈ binDual (C r)) ≤
      (1 - (2 : ℝ) ^ ((minDim C : ℝ) - n) * eps) *
        (2 : ℝ) ^ (1 - (minDim C : ℝ) + Module.finrank (ZMod 2) B) + eps - 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
