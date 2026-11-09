-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_order_reduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.order_reduction
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T03:49:45.038684+00:00
-- url     : https://prove2.me/theorems/44bcda97-70f0-4361-8bcf-89bdf5fc2856
-- title:
--   §1 example 1: multiplicative order from a stabilizer
-- statement:
--   Let $q\ge2$ and let $g$ be a unit modulo $q$. For integer $m$, set $F_g(m,x)=g^m x$ on $\mathbb Z/q\mathbb Z$, and let $r=\operatorname{ord}(g)$. Then
--
--   $$
--   r>0,\qquad \{m\in\mathbb Z:F_g(m,1)=1\}=r\mathbb Z.
--   $$
--
--   Moreover, $F_g(r,1)=1$, and every positive natural number $s$ with $F_g(s,1)=1$ satisfies $r\le s$. Thus the positive canonical stabilizer generator is precisely the multiplicative order.
--
--   This is the algebraic reduction to a stabilizer, without importing the separately cited randomized factoring reduction.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 4, §1 example 1: multiplicative order from a stabilizer

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.4, example 1: the stabilizer at one is (orderOf g) Z, whose positive
canonical generator is exactly the multiplicative order. No factoring reduction is added. -/
theorem order_reduction (q : ℕ) (hq : 2 ≤ q) (g : (ZMod q)ˣ) :
    0 < orderOf g ∧
    (∀ m : ℤ, orderAction g m 1 = 1 ↔ ∃ t : ℤ, m = (orderOf g : ℤ) * t) ∧
    orderAction g (orderOf g : ℤ) 1 = 1 ∧
    ∀ r : ℕ, 0 < r → orderAction g (r : ℤ) 1 = 1 → orderOf g ≤ r := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
