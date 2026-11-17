-- Prove2me | Theorems.Thm_RSCapacity_Supplement_theorem_6_5
-- name    : RSCapacity.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:28:32.130518+00:00
-- url     : https://prove2.me/theorems/8a7c7993-009e-4d01-bbee-e9a7cbc6f18b
-- title:
--   Theorem 6.5 (Parametric jet decomposition)
-- statement:
--   Fix integers $r,B\ge0$. There is an effective constant $C_0=C_0(r,B)$ with the following property. Let $F$ be algebraically closed of characteristic $p$, let $0\le d<p$, and let $0\ne Q\in F[Z,X,Y_0,\dots,Y_r]$ be $Z$-primitive and satisfy
--   $$\deg_Z Q,\ \deg_X Q\le D,\qquad \deg^{\mathrm{tot}}_Y Q\le B<p,\qquad D\ge2.\tag{56}$$
--   Then there are a finite set $E_Q\subseteq F$ and affine algebraic sets $V_1,\dots,V_t\subseteq\mathbb A^{d+2}$ such that
--   $$|E_Q|+\sum_{j=1}^t\operatorname{cdeg}(V_j)\le(D+d+2)^{C_0},\tag{57}$$
--   $$\dim V_j\le r+1\quad\text{for every } j,\tag{58}$$
--   and every $(z,p)\in\mathrm{Sol}_d(Q)$ with $z\notin E_Q$ belongs to $\bigcup_j V_j$.
--
--   Outside a small exceptional set of parameter values, the polynomial solutions of the parametric differential equation $Q(z,X,P,P^{[1]},\dots,P^{[r]})\equiv0$ lie on a family of varieties of dimension at most $r+1$ and polynomially bounded cumulative degree. This is the geometric input of the proximity-gap theorem.
--
--   **Formalization Note** $C_0$ is a natural number chosen after $r,B$. $F[Z,X,Y_0,\dots,Y_r]$ is `MvPolynomial (Fin (r + 3)) F` with $Z=0$, $X=1$, $Y_j=j+2$; $\deg_Z$, $\deg_X$ are `degreeOf 0`, `degreeOf 1`, and $\deg^{\mathrm{tot}}_Y$ is the weighted total degree with weight $1$ on each $Y_j$ and $0$ on $Z,X$. Dimension and cumulative degree are the published `algDim` and `cdeg`; (57) is one inequality in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--   - encoding: F of characteristic p with d < p and B < p → d < ringChar F and B < ringChar F; reason: characteristic 0 is excluded exactly as on the page (d < p, B < p), as in the published Corollary 7.1
--   - encoding: effective constant C_0(r, B) → a natural number chosen after r, B and before F, d, D, Q; reason: a real exponent can be rounded up since D + d + 2 ≥ 1
--   - encoding: F an algebraically closed field → a field in Type (universe 0) with IsAlgClosed; reason: Lean universe convention, as in the published Corollary 7.1
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Theorem 6.5 with Equations (55)–(58), p.25 (PDF 27)

import Mathlib
import Definitions.Def_RSCapacity_JetCoefficients
import Definitions.Def_RSCapacity_AffineGeometry
import Definitions.Def_RSCapacity_Supplement_Defs

open Polynomial

set_option autoImplicit false

namespace RSCapacity.Supplement

/-- **Theorem 6.5 (Parametric jet decomposition).** Jeronimo, arXiv:2609.05870 (held version of
November 1, 2026, sha256 9a0069bd…), Theorem 6.5, p.25 (PDF 27), with (55)–(58). Fix integers
r, B ≥ 0. There is an effective constant C_0 = C_0(r, B) with the following property. Let F be
algebraically closed of characteristic p, let 0 ≤ d < p, and let 0 ≠ Q ∈ F[Z, X, Y_0, …, Y_r] be
Z-primitive and satisfy deg_Z Q, deg_X Q ≤ D, deg^tot_Y Q ≤ B < p, D ≥ 2 (56). Then there are a
finite set E_Q ⊆ F and affine algebraic sets V_1, …, V_t ⊆ 𝔸^{d+2} such that
|E_Q| + ∑_{j=1}^{t} cdeg(V_j) ≤ (D + d + 2)^{C_0} (57), dim V_j ≤ r + 1 for every j (58), and every
(z, p) ∈ Sol_d(Q) with z ∉ E_Q belongs to ⋃_j V_j.

**Formalization Note.** C_0 is a natural number chosen after r, B and before F, d, D, Q.
"Characteristic p" with d < p and B < p is `d < ringChar F ∧ B < ringChar F` (characteristic 0
is excluded, as in the published Corollary 7.1). F ranges over fields in `Type`.
F[Z, X, Y_0, …, Y_r] is `MvPolynomial (Fin (r + 3)) F` (Z = 0, X = 1, Y_j = j + 2);
deg_Z = `degreeOf 0`, deg_X = `degreeOf 1`, deg^tot_Y = weighted total degree for `yWeight3 r`.
(57) is one inequality in ℕ∞ (`cdeg` is ℕ∞-valued); dim is `algDim` (the empty set has
dimension ⊥). A point of 𝔸^{d+2} has coordinate 0 = z and coordinate j + 1 = p_j. -/
theorem theorem_6_5 (r B : ℕ) :
    ∃ C₀ : ℕ, ∀ (F : Type) [Field F] [IsAlgClosed F] (d D : ℕ), d < ringChar F →
      B < ringChar F → 2 ≤ D →
      ∀ Q : MvPolynomial (Fin (r + 3)) F, Q ≠ 0 → IsZPrimitive Q → Q.degreeOf 0 ≤ D →
        Q.degreeOf 1 ≤ D → Q.weightedTotalDegree (yWeight3 r) ≤ B →
        ∃ (E : Finset F) (t : ℕ) (V : Fin t → Set (Fin (d + 2) → F)), (∀ j, IsAlgSet (V j)) ∧
          (E.card : ℕ∞) + ∑ j, cdeg (V j) ≤ (((D + d + 2) ^ C₀ : ℕ) : ℕ∞) ∧
          (∀ j, algDim (V j) ≤ (((r + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) ∧
          ∀ x ∈ solLocus r d Q, x 0 ∉ E → ∃ j, x ∈ V j := by sorry

end RSCapacity.Supplement
