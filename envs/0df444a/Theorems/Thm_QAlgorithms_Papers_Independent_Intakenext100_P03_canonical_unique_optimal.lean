-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_canonical_unique_optimal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.canonical_unique_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:49:35.567004+00:00
-- url     : https://prove2.me/theorems/189298dd-8f81-4872-a3de-b318f0829566
-- title:
--   Uniqueness and optimality of the canonical form
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$.
--
--   For an axis $p\in\{x,y,z\}$ with Pauli matrix $P$, write $U_p(\theta)=\frac{1+e^{i\theta}}2I+\frac{1-e^{i\theta}}2P$. A canonical pair consists of an ordered finite list $(p_i,a_i)_{i=1}^m$ and an actual matrix $D$, with consecutive axes distinct, $1\le a_i<n/2$, $D$ proportional to an element of $C$, and $U=(\prod_{i=1}^m U_{p_i}(a_i\pi/n))D$. Products have the printed left-to-right order, and the empty list is permitted. Let $T_n(U)$ be the minimum number of positive elementary $U_z(\pi/n)$ occurrences among Clifford/rotation words implementing $U$ up to one global phase; Clifford gates have zero cost. Every $U\in G_n$ has exactly one canonical pair, and every canonical pair satisfies
--
--   $$\sum_{i=1}^m\min(a_i,n/2-a_i)=T_n(U).$$
--
--   Uniqueness includes the actual residual matrix $D$, not the phase and Clifford witnesses separately. The empty form has cost zero. This identifies canonical cost with optimal synthesis cost.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 10, Corollary 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Corollary 4.2, PDF pp.10-11: uniqueness of the entire data pair including
D, and optimality modulo one global phase, including the empty form. -/
theorem canonical_unique_optimal (n : ℕ) (hn : 0 < n) (heven : Even n)
    (U : Mat) (hU : U ∈ cyclotomicGroup n) :
    (∃! d : CanonicalData, IsCyclotomicCanonical n U d) ∧
    ∀ d : CanonicalData, IsCyclotomicCanonical n U d →
      canonicalCost n d = minimumRotationCost n U := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
