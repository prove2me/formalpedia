-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_normalized_numerators
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.normalized_numerators
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:53:26.635298+00:00
-- url     : https://prove2.me/theorems/9abba75e-3ab4-4fe6-9028-8527106b6e68
-- title:
--   Coprime normalized trigonometric numerators
-- statement:
--   Let $n$ be a positive even integer. Put $\zeta_m=e^{2\pi i/m}$, $R_n=\mathbb Z[\zeta_{2n},1/2]$, $U_z(\theta)=\operatorname{diag}(1,e^{i\theta})$, and $G_n=\langle C,U_z(\pi/n)\rangle$, where $C=\langle H_0,S\rangle$, $H_0=\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S=\operatorname{diag}(1,i)$.
--
--   Write $n=2^ks$ with $k\ge1$ and positive odd $s$. Define $q_a=2^{k-1}-2^{k-j}$ if $n/\gcd(a,n)=2^j$, and $q_a=2^{k-1}$ otherwise. Set $\alpha=2^{1/2^{k-1}}$ and $\beta=2$ for $k=1$, $\beta=2\cos(\pi/2^k)$ for $k\ge2$. For $1\le a<n/2$, set $c_a=\alpha^{q_a}\cos(\pi a/n)$ and $s_a=\alpha^{q_a}\sin(\pi a/n)$, equivalently the piecewise normalization (32). Let $K=\mathbb Q(\{c_a,s_a:1\le a<n/2\},\alpha)$ and $\mathcal O_K$ be its ring of integers. Then
--
--   $$c_a,s_a\in\mathcal O_K,\qquad c_a\mathcal O_K+\alpha\mathcal O_K=s_a\mathcal O_K+\alpha\mathcal O_K=\mathcal O_K.$$
--
--   If $n/\gcd(a,n)$ is a power of two, then also $c_a,s_a\in\mathcal O_K^\times$. Units and coprimality are taken in this ring of integers. These numerators control denominator cancellation.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 15, Lemma 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Lemma 6.1, PDF pp.15-16: integrality, coprimality and the conditional
unit assertion in O_K. The normalization is equation (32), equivalently (33). -/
theorem normalized_numerators (n k s : ℕ) (hk : 1 ≤ k) (hs : 0 < s)
    (hodd : Odd s) (hfactor : n = 2 ^ k * s)
    (a : ℕ) (ha : 1 ≤ a) (halt : a < n / 2) :
    InIntegers (numeratorField n k) (cosineNumerator n k a) ∧
    InIntegers (numeratorField n k) (sineNumerator n k a) ∧
    IntegerCoprime (numeratorField n k) (cosineNumerator n k a) (denominatorAlpha k) ∧
    IntegerCoprime (numeratorField n k) (sineNumerator n k a) (denominatorAlpha k) ∧
    (IsTwoPower (n / Nat.gcd a n) →
      IntegerUnit (numeratorField n k) (cosineNumerator n k a) ∧
      IntegerUnit (numeratorField n k) (sineNumerator n k a)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
