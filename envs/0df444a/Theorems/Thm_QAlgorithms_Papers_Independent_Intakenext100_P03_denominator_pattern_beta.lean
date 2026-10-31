-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_denominator_pattern_beta
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.denominator_pattern_beta
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:48:50.864271+00:00
-- url     : https://prove2.me/theorems/9466aafc-e79c-49d2-8312-ef1ee346d0d2
-- title:
--   Denominator exponent pattern with beta
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$.
--
--   For an axis $p\in\{x,y,z\}$ with Pauli matrix $P$, write $U_p(\theta)=\frac{1+e^{i\theta}}2I+\frac{1-e^{i\theta}}2P$. A canonical pair consists of an ordered finite list $(p_i,a_i)_{i=1}^m$ and an actual matrix $D$, with consecutive axes distinct, $1\le a_i<n/2$, $D$ proportional to an element of $C$, and $U=(\prod_{i=1}^m U_{p_i}(a_i\pi/n))D$. Products have the printed left-to-right order, and the empty list is permitted.
--
--   Write $n=2^ks$ with $k\ge1$ and positive odd $s$. Define $q_a=2^{k-1}-2^{k-j}$ if $n/\gcd(a,n)=2^j$, and $q_a=2^{k-1}$ otherwise. Set $\alpha=2^{1/2^{k-1}}$ and $\beta=2$ for $k=1$, $\beta=2\cos(\pi/2^k)$ for $k\ge2$.
--
--   Use ordered Pauli axes $X,Y,Z$ and the homomorphic Bloch matrix $B(U)_{ij}=\frac12\operatorname{Re}\operatorname{tr}(P_iUP_jU^\dagger)$. This transposes printed equation (9), as required by the source's left-cancellation proof and row patterns.
--
--   Let $U\in G_n$ with $B(U)\notin B(C)$, take any canonical pair, and set $N=\sum_iq_{a_i}$. Work in the ring of integers $\mathcal O_F$ of $F=\operatorname{Frac}(R_n\cap\mathbb R)$. A reduced exponent of a nonzero entry $z$ means $z=w/\beta^r$, with $r\in\mathbb N$, $w\in\mathcal O_F$, and $w$ not divisible by $\beta$. Coprimality means that the principal ideals sum to $\mathcal O_F$.
--
--   1. Every nonzero entry has a reduced exponent.
--   2. The global maximum is attained and satisfies
--
--   $$\max_{i,j:B(U)_{ij}\ne0}r_{ij}=N.$$
--
--   Exactly two rows contain an entry at exponent $N$ with numerator coprime to $\beta$.
--   3. Exactly one row has no entry at exponent $N$. It is the row indexed by the first axis $p_1$, and its attained maximum is
--
--   $$\max_{j:B(U)_{p_1j}\ne0}r_{p_1j}=N-q_{a_1}.$$
--
--   That row contains an entry at this exponent with numerator coprime to $\beta$. The non-Clifford premise guarantees a nonempty list.
--
--   The pattern exposes the leading canonical axis while retaining the stronger coprimality conclusion.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 10, Theorem 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Theorem 4.1(a)-(c), PDF pp.9-10, proof p.18. The homomorphic Bloch
correction in homomorphicBloch transposes printed (9), justified by row cancellation
on pp.11,17; independent moderation is required. -/
theorem denominator_pattern_beta (n k s : ℕ) (hk : 1 ≤ k) (hs : 0 < s)
    (hodd : Odd s) (hfactor : n = 2 ^ k * s)
    (U : Mat) (hU : U ∈ cyclotomicGroup n) (hnot : homomorphicBloch U ∉ blochCliffords)
    (d : CanonicalData) (hd : IsCyclotomicCanonical n U d) :
    ∃ p a rest, d.1 = (p, a) :: rest ∧
      DenominatorPattern (realCyclotomicField n) (denominatorBeta k) (homomorphicBloch U)
        (canonicalTotalWeight n k d) (denominatorWeight n k a) p := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
