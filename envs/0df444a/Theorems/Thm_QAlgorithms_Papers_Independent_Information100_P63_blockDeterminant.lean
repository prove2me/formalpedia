-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_blockDeterminant
-- name    : QAlgorithms.Papers.Independent.Information100.P63.blockDeterminant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:35:00.418851+00:00
-- url     : https://prove2.me/theorems/b06de601-9441-47a0-a9a8-c891ea468776
-- title:
--   Block determinant inequality for phase damping
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Let $d\ge2$ and $m\ge1$. Let $U$ be a unitary matrix whose columns $u_i$ form a basis uniform relative to the computational basis: $|U_{ji}|^2=1/d$ for all $i,j$. For any positive semidefinite $R$ on $\mathbb C^d\otimes\mathbb C^m$, define $R_{ij}=(\langle u_i|\otimes I)R(|u_j\rangle\otimes I)$. Put $P_i=|u_i\rangle\langle u_i|$ and $\Delta_{p,d}(X)=(1-p)X+p\sum_iP_iXP_i$. For $0\le p\le d^2/(d^2-1)$, $\alpha=1-p+p/d$, $\beta=p/d$, and every $t>0$,
--
--   $$
--   L_t((\Delta_{p,d}\otimes\mathrm{id})(R))\ge\frac1d\sum_{i=1}^d\big[L_t(d\alpha R_{ii})+(d-1)L_t(d\beta R_{ii})\big].
--   $$
--
--   The bound applies to unnormalized positive operators and includes $p=0,1$ and the allowed range above one.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 5, Lemma 3, Eq. (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3, Eq.(14), PDF pp.4–5. `U` has the uniform orthonormal basis as columns;
`R` is positive without normalization. Both channel endpoints are included. -/
theorem blockDeterminant (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hu : ∀ i j, Complex.normSq ((U : Mat (Fin d)) j i) = 1 / (d : ℝ))
    (R : Mat (Fin d × Fin m)) (hR : R.PosSemidef) (p t : ℝ)
    (hp : 0 ≤ p) (hpmax : p ≤ pMax d) (ht : 0 < t) :
    (1 / (d : ℝ)) * ∑ i : Fin d,
      (logDet t (((d : ℝ) * alpha d p : ℂ) • block (U : Mat (Fin d)) R i i) +
      (d-1 : ℝ) * logDet t (((d : ℝ) * beta d p : ℂ) • block (U : Mat (Fin d)) R i i)) ≤
      logDet t (phaseDamping p (U : Mat (Fin d)) R) := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end
