-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_canonical_exists
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.canonical_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:48:10.155957+00:00
-- url     : https://prove2.me/theorems/9a7db8fb-147b-4bff-9b84-2782ecb7b08c
-- title:
--   Existence of an alternating-axis canonical decomposition
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$.
--
--   For an axis $p\in\{x,y,z\}$ with Pauli matrix $P$, write $U_p(\theta)=\frac{1+e^{i\theta}}2I+\frac{1-e^{i\theta}}2P$. A canonical pair consists of an ordered finite list $(p_i,a_i)_{i=1}^m$ and an actual matrix $D$, with consecutive axes distinct, $1\le a_i<n/2$, $D$ proportional to an element of $C$, and $U=(\prod_{i=1}^m U_{p_i}(a_i\pi/n))D$. Products have the printed left-to-right order, and the empty list is permitted. For every $U\in G_n$, there is such a pair:
--
--   $$\exists\,((p_i,a_i)_{i=1}^m,D),\qquad U=\left(\prod_{i=1}^mU_{p_i}(a_i\pi/n)\right)D.$$
--
--   This provides the canonical syntax without assuming its later uniqueness or optimality.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 7, Lemma 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Lemma 3.1, PDF pp.6-8: existence, without assuming the stronger
optimality identity proved there and stated separately in Corollary 4.2. -/
theorem canonical_exists (n : ℕ) (hn : 0 < n) (heven : Even n)
    (U : Mat) (hU : U ∈ cyclotomicGroup n) :
    ∃ d : CanonicalData, IsCyclotomicCanonical n U d := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
