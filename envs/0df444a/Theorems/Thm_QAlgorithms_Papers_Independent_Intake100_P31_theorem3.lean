-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_theorem3
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.theorem3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:46:31.760971+00:00
-- url     : https://prove2.me/theorems/41a47219-7789-46d9-8afb-9b5cd2adbf4e
-- title:
--   Theorem 3, bound clause: dual of a universal subcode family
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. Fix a code $B$ of dimension $m$ and suppose every $C_r\le B$. Assume $\varepsilon\ge0$ and $\Pr_r[x\in C_r]\le\varepsilon2^{t-m}$ for every $x\in B\setminus\{0\}$, with $t=t_{\min}$. The duals extend $B^\perp$, have maximum dimension $n-t$, and are extended-code universal with parameter $2(1-2^{t-m}\varepsilon)+(\varepsilon-1)2^t$. Explicitly,
--
--   $$\forall x\notin B^\perp,\quad\Pr_r[x\in C_r^\perp]\le(1-2^{t-m}\varepsilon)2^{1-t}+\varepsilon-1.$$
--
--   The sharpness clause is separately deferred.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 6, Theorem 3, bound clause: dual of a universal subcode family

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.6, Theorem 3, bound clause. The duals extend B-perp; the printed
parenthetical subcode/extended-code terminology is reversed. -/
theorem theorem3 {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (B : BinaryLinearCode n) (C : I → BinaryLinearCode n) (eps : ℝ) (heps : 0 ≤ eps)
    (hu : SubUniversalAt B C (minDim C) eps) :
    maxDim (fun r => binDual (C r)) = n - minDim C ∧
    ExtUniversalAt (binDual B) (fun r => binDual (C r)) (n - minDim C)
      (dualParameter (Module.finrank (ZMod 2) B) (minDim C) eps) ∧
    ∀ x : BinaryBlock n, x ∉ binDual B → seedProbability (fun r => x ∈ binDual (C r)) ≤
      (1 - (2 : ℝ) ^ ((minDim C : ℝ) - Module.finrank (ZMod 2) B) * eps) *
        (2 : ℝ) ^ (1 - (minDim C : ℝ)) + eps - 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
