-- Prove2me | Theorems.Thm_StableMSR_Recovery_polynomial_minwise
-- name    : StableMSR.Recovery.polynomial_minwise
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T15:22:24.148226+00:00
-- url     : https://prove2.me/theorems/fb397c83-c3a9-4f66-995f-3997e6c1f332
-- title:
--   Explicit fixed-degree polynomial minwise bound
-- statement:
--   Let $q$ be a prime and $m\ge0$, with $q\ge8193$ and $q\ge4m^2$. For each coefficient vector $a\in\mathbb F_q^{8193}$, define a hash on the ordered input keys $0,\ldots,m-1$ by
--   $$h_a(x)=\operatorname{val}\!\left(\sum_{i=0}^{8192}a_i x^i\right),$$
--   where $\operatorname{val}$ takes the representative in $\{0,\ldots,q-1\}$. Order the keys by increasing hash value, breaking ties by increasing input index. For every nonempty subset $T$ and every $z\in T$, uniformly sampling the coefficient vector satisfies
--   $$\Pr_a[z\text{ is first in }T]\le\frac{3}{2|T|}.$$
--
--   The probability is the number of successful coefficient vectors divided by $q^{8193}$. Different vectors that produce the same order are counted separately. Thus the result supplies the finite multiset-of-orders interpretation used in the deterministic order-family argument.
--
--   This is an explicit, nonoptimized constant-degree realization of the minwise bound used in Appendix B. The proof establishes the limited-independence, moment, and tie-breaking estimates internally; it does not assume a minwise theorem. The theorem takes the prime $q$ as a parameter and does not assert a prime-generation or machine-enumeration runtime.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix B, https://arxiv.org/html/2611.03547v1; an explicit constant-degree specialization of the minwise construction, with the finite-sample analysis proved directly. Related primary source: P. Indyk, A Small Approximately Min-Wise Independent Family of Hash Functions, https://people.csail.mit.edu/indyk/minwise.pdf. Degree 8192 is an explicit nonoptimized choice in this formalization, rather than a claimed optimal constant from the source.

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery

theorem polynomial_minwise (q m : ℕ) [Fact q.Prime]
    (hq : 8193 ≤ q) (hm : 4*m^2 ≤ q) :
    let hash : (Fin 8193 → ZMod q) → Fin m → ℕ := fun a x =>
      (∑ i : Fin 8193, a i * (x.val : ZMod q) ^ (i : ℕ)).val
    ∀ (T : Finset (Fin m)) (z : Fin m), z ∈ T →
      (((Finset.univ : Finset (Fin 8193 → ZMod q)).filter (fun a =>
        ∀ y ∈ T, y ≠ z →
          hash a z < hash a y ∨ (hash a z = hash a y ∧ z < y))).card : ℝ) /
        (q : ℝ)^8193 ≤ 3 / (2*(T.card : ℝ)) := by sorry

end StableMSR.Recovery
