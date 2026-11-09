-- Prove2me | Theorems.Thm_RSCapacity_proposition_4_7
-- name    : RSCapacity.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:49.195387+00:00
-- url     : https://prove2.me/theorems/f37dba0a-3b34-48c8-8fd3-7c157346f4e9
-- title:
--   Proposition 4.7 (Optimized sparse interpolant)
-- statement:
--   Fix $\vartheta\in(0,1)$ and put $u_0=1/(1-\vartheta)$. There are constants $r_0$ and $a_\vartheta>0$ such that the following holds. Let $F$ be a field, $\alpha_1,\dots,\alpha_n\in F$ distinct and $S_1,\dots,S_n\subseteq F$ finite of total incidence $M$. Let $2\le K\le A\le n$ and $1\le r<K$ be integers with
--   $$\frac{A}{K-1}\ge u_0,\qquad r\ge r_0,\qquad m=r^3,\qquad M\le a_\vartheta(K-1)\frac{r^\vartheta}{\log^4(er)} .$$
--   Put $\delta=1/\log(er)$, $c=u_0-2\delta$ and $s=u_0-\delta$. Then there is a nonzero $Q\in\mathcal Q(A,K,r,m,c,s)$ such that
--   1. $Q$ obeys the local constraints (24) at $(\alpha_i,y)$ for every $i$ and every $y\in S_i$;
--   2. every $P\in F[X]$ with $\deg P<K$ and at least $A$ list hits satisfies $Q(X,P,P^{[1]},\dots,P^{[r]})=0$.
--
--   This is the interpolation step of the decoder at the full slack: the list size $M$ may grow like $(K-1)r^\vartheta$.
--
--   Differences from the source:
--   - reading: there is a nonzero interpolant satisfying every incidence constraint → a nonzero element of 𝒬(A, K, r, r³, c, s) with the shape (39) of the proof, δ = 1/log(er), c = u_0 − 2δ, s = u_0 − δ, obeying (24) at every (α_i, y) with y ∈ S_i; reason: the interpolant of the proposition is the one built from (39); fixing the shape is the stronger reading
--   - encoding: the instance (field, points, lists) → any field F, an injective α : Fin n → F, finite sets S_i; reason: Definition 3.1 and Corollary 4.8 (any field F)
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Proposition 4.7, p.18 (PDF 20); Equation (39), p.18

import Mathlib
import Definitions.Def_RSCapacity_ListRecovery
import Definitions.Def_RSCapacity_DiffSubst
import Definitions.Def_RSCapacity_LocalConstraints

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-- **Proposition 4.7 (Optimized sparse interpolant).** Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…),
Proposition 4.7, p.18 (PDF 20). Fix ϑ ∈ (0, 1). There are effective constants r_0 and a_ϑ > 0 such
that, for integers 2 ≤ K ≤ A ≤ n and 1 ≤ r < K, whenever A/(K − 1) ≥ u_0 := 1/(1 − ϑ), r ≥ r_0,
m = r³, and M ≤ a_ϑ (K − 1) r^ϑ / log⁴(er) (38), there is a nonzero interpolant satisfying every
incidence constraint, and every degree-below-K polynomial with at least A list hits satisfies its
differential equation.

**Formalization Note.** The instance is a field F, distinct α_1, …, α_n and finite sets S_i of
total incidence M (Definition 3.1). The interpolant is a nonzero element of 𝒬(A, K, r, m, c, s) with
the optimized shape (39): δ = 1/log(er), c = u_0 − 2δ, s = u_0 − δ. "Every incidence constraint" is
(24) at (α_i, y) for each y ∈ S_i; "its differential equation" is Q(X, P, P^{[1]}, …, P^{[r]}) = 0.
r_0 and a_ϑ depend on ϑ only. -/
theorem proposition_4_7 (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) :
    ∃ r₀ : ℕ, ∃ a : ℝ, 0 < a ∧
      ∀ (F : Type) [Field F] (n : ℕ) (α : Fin n → F), Function.Injective α →
      ∀ (S : Fin n → Finset F) (K A r : ℕ), 2 ≤ K → K ≤ A → A ≤ n → 1 ≤ r → r < K →
        1 / (1 - ϑ) ≤ (A : ℝ) / ((K : ℝ) - 1) → r₀ ≤ r →
        (incidence S : ℝ) ≤ a * ((K : ℝ) - 1) * (r : ℝ) ^ ϑ / Real.log (Real.exp 1 * r) ^ 4 →
        ∃ Q ∈ interpSpace F A K r (r ^ 3)
            (1 / (1 - ϑ) - 2 * (1 / Real.log (Real.exp 1 * r)))
            (1 / (1 - ϑ) - 1 / Real.log (Real.exp 1 * r)),
          Q ≠ 0 ∧ (∀ i, ∀ y ∈ S i, ObeysLocal r (r ^ 3) (α i) y Q) ∧
          ∀ P : F[X], P.degree < K → A ≤ hits α S P → diffEval Q P = 0 := by sorry

end RSCapacity
