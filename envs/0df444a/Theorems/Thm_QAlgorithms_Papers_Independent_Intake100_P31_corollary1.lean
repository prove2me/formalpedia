-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_corollary1
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.corollary1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:43:59.615635+00:00
-- url     : https://prove2.me/theorems/999eaea4-7914-4359-971b-d0f5256cd7dd
-- title:
--   Corollary 1: optimal and ordinary universality under duality
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. Define $\varepsilon_{\rm opt}(n,t)=(2^n-2^{n-t})/(2^n-1)$. Then:
--
--   1. Minimum-dimension optimal universality of $C_r$ implies maximum-dimension optimal universality of $C_r^\perp$, with parameter $\varepsilon_{\rm opt}(n,n-t_{\min})$.
--   2. Minimum-dimension universality with parameter one implies maximum-dimension universality of the dual with parameter two.
--   3. There exist $d>t>0$, a finite nonempty uniform family $D_r\le\mathbb F_2^d$ of minimum dimension $t$, and a chosen $\varepsilon>1$ such that
--
--   $$D_r\text{ is }\varepsilon\text{-almost universal},\qquad \exists x\ne0:\Pr_r[x\in D_r^\perp]=1.$$
--
--   The existential choice of epsilon is part of the third assertion.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 5, Corollary 1: optimal and ordinary universality under duality

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.5, Corollary 1, all three clauses. The counterexample chooses epsilon,
rather than promising a witness for every preassigned epsilon greater than one. -/
theorem corollary1 {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (C : I → BinaryLinearCode n) :
    (UniversalAt C (minDim C) (optimalParameter n (minDim C)) →
      UniversalAt (fun r => binDual (C r)) (maxDim (fun r => binDual (C r)))
        (optimalParameter n (n - minDim C))) ∧
    (UniversalAt C (minDim C) 1 →
      UniversalAt (fun r => binDual (C r)) (maxDim (fun r => binDual (C r))) 2) ∧
    (∃ (d t N : ℕ), 0 < d ∧ 0 < t ∧ t < d ∧
      ∃ (D : Fin (N + 1) → BinaryLinearCode d) (eps : ℝ), 1 < eps ∧ minDim D = t ∧
        UniversalAt D t eps ∧ ∃ x : BinaryBlock d, x ≠ 0 ∧
          seedProbability (fun r => x ∈ binDual (D r)) = 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
