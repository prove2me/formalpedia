-- Prove2me | Theorems.Thm_RSCapacity_corollary_7_1
-- name    : RSCapacity.corollary_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:03.021259+00:00
-- url     : https://prove2.me/theorems/aed99a15-de5e-4c9a-869c-68145c9861f8
-- title:
--   Corollary 7.1 (A parameter-free solution cover)
-- statement:
--   Fix $r,B\ge0$. There are constants $C_{r,B}$ and $C_0=C_0(r,B)$ such that the following holds. Let $F$ be algebraically closed of characteristic $p$, let $0\le d<p$, $B<p$ and $D\ge2$. For a nonzero $Q(X,Y_0,\dots,Y_r)\in F[X,Y_0,\dots,Y_r]$ with $\deg_XQ\le D$ and $\deg^{\mathrm{tot}}_YQ\le B$, the coefficient vectors of all degree-at-most-$d$ solutions of $Q(X,P,P^{[1]},\dots,P^{[r]})\equiv0$ are contained in a union of affine algebraic sets $W_1,\dots,W_t\subseteq\mathbb A^{d+1}$ with
--   $$\dim W_j\le r,\qquad \sum_j\operatorname{cdeg}(W_j)\le C_{r,B}(D+d+1)(d+1)^r\le(D+d+2)^{C_0}.$$
--
--   The cover has dimension at most $r$ and degree polynomial in $d$, independently of the field: this is what makes the final list bound independent of $q$.
--
--   Differences from the source:
--   - encoding: F of characteristic p with d < p and B < p → d < ringChar F and B < ringChar F; reason: characteristic 0 is excluded exactly as on the page
--   - encoding: effective constants C_{r,B}, C_0 → natural numbers chosen after r, B; reason: a real constant can be rounded up
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Corollary 7.1, p.29 (PDF 31)

import Mathlib
import Definitions.Def_RSCapacity_DiffSubst
import Definitions.Def_RSCapacity_AffineGeometry

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-- **Corollary 7.1 (A parameter-free solution cover).** Jeronimo, arXiv:2609.05870 (held version
of November 1, 2026, sha256 9a0069bd…), Corollary 7.1, p.29 (PDF 31). Fix r, B ≥ 0. There are
effective constants C_{r,B} and C_0 = C_0(r, B) such that the following holds. Let F be
algebraically closed of characteristic p, let 0 ≤ d < p, let B < p, and let D ≥ 2. For a nonzero
Q(X, Y_0, …, Y_r) ∈ F[X, Y_0, …, Y_r], deg_X Q ≤ D, deg^tot_Y Q ≤ B, the coefficient vectors of
all degree-at-most-d solutions of Q(X, P, P^{[1]}, …, P^{[r]}) ≡ 0 are contained in a union of
affine algebraic sets W_1, …, W_t ⊆ 𝔸^{d+1} with dim W_j ≤ r,
∑_j cdeg(W_j) ≤ C_{r,B} (D + d + 1)(d + 1)^r ≤ (D + d + 2)^{C_0}.

**Formalization Note.** C_{r,B} and C_0 are natural numbers chosen after r, B and before F, d, D,
Q. "Characteristic p" with d < p and B < p is `d < ringChar F ∧ B < ringChar F` (characteristic 0
excluded, as on the page). A degree-at-most-d polynomial is P_p = ∑_{j ≤ d} p_j X^j with coefficient
vector p ∈ F^{d+1}. Both inequalities of the chain are conjuncts. -/
theorem corollary_7_1 (r B : ℕ) :
    ∃ C C₀ : ℕ, ∀ (F : Type) [Field F] [IsAlgClosed F] (d D : ℕ), d < ringChar F →
      B < ringChar F → 2 ≤ D →
      ∀ Q : MvPolynomial (Fin (r + 2)) F, Q ≠ 0 → Q.degreeOf 0 ≤ D →
        Q.weightedTotalDegree (yWeight r) ≤ B →
        ∃ (t : ℕ) (W : Fin t → Set (Fin (d + 1) → F)), (∀ j, IsAlgSet (W j)) ∧
          (∀ j, algDim (W j) ≤ ((r : ℕ∞) : WithBot ℕ∞)) ∧
          {p : Fin (d + 1) → F | diffEval Q (polyOfVec p) = 0} ⊆ ⋃ j, W j ∧
          ∑ j, cdeg (W j) ≤ ((C * (D + d + 1) * (d + 1) ^ r : ℕ) : ℕ∞) ∧
          C * (D + d + 1) * (d + 1) ^ r ≤ (D + d + 2) ^ C₀ := by sorry

end RSCapacity
