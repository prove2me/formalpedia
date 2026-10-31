-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_explicit_chain_pairing_table
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.explicit_chain_pairing_table
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:12:36.284159+00:00
-- url     : https://prove2.me/theorems/577966f6-5e03-48a7-be56-abdfd031a00f
-- title:
--   Remark 14 — explicit chain pairing table (corrected conjugation sign)
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For $|\lambda|=1$, define
--   $$T_{ij}(v)=\frac{\Omega_{\mathbb C}(N_\lambda^i v,N_{\bar\lambda}^j\bar v)}{\lambda^i\bar\lambda^j},\qquad i,j\ge0.$$
--   Suppose $\lambda$ is nonreal of unit norm, its maximal height is $2k$, and $v$ is a vector of that height normalized as in section 4.2: $s\in\{1,-1\}$, $T_{kk}=-si$, $T_{ij}=0$ for $i,j<k$, and $T_{k,k-1}=si/2$ when $k>0$. Then
--   $$\begin{aligned}T_{ij}&=0&&\text{if }i+j\ge2k+1\text{ or }0\le i,j<k,\\T_{k-r,k+r}&=(-1)^{r+1}si&&0\le r\le k,\\T_{k-r,k+m}&=(-1)^{r+1}\frac{si}{2}\frac{(r+m)(r-1)!}{m!(r-m)!}&&0\le m\le r\le k,\ r>1,\\T_{ij}&=-\overline{T_{ji}}&&i,j\ge0.\end{aligned}$$
--   The last line corrects the printed missing minus sign using (17) and the table's own $r=0$ entry. Every factorial argument is nonnegative.
--
--
--   This gives the entire explicit pairing table and discloses the source correction.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 22, Remark 14 — explicit chain pairing table (corrected conjugation sign)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P39

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P39

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse only the pinned accepted substrate, with definitionally identical coordinate models.
-- The imported symplectic predicate preserves -Omega0, equivalent to preserving Omega0.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

open QAlgorithms.Papers.Independent.Gap50repair.P01
  (Coord GroupedRealMatrix omegaMatrix omegaR omegaC shifted generalizedSpace
    IsEigenvalue HasNilpotentHeight restrictedKernel GeneralizedQuotient)

/-- PDF p.22, Remark 14. Printed: T_ij=conjugate(T_ji) on the last line.
Changed: MINUS conjugate, consistently with (17) and T_kk=-s*i at r=0.
The factorial ranges are exactly the printed nonnegative ranges. -/
theorem explicit_chain_pairing_table {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz : ‖z‖ = 1) (hreal : z.im ≠ 0) (k : ℕ)
    (v : CVec n) (hpmax : HasNilpotentHeight A z (2 * k))
    (hp : VectorHeight A z v (2 * k))
    (s : ℤ) (hs : s = 1 ∨ s = -1) (hpair : chainT A z v k k = -(s : ℂ) * Complex.I)
    (hlow : ∀ i < k, ∀ j < k, chainT A z v i j = 0)
    (hnext : 0 < k → chainT A z v k (k - 1) = (s : ℂ) * Complex.I / 2) :
    (∀ i j : ℕ, 2 * k + 1 ≤ i + j → chainT A z v i j = 0) ∧
    (∀ i < k, ∀ j < k, chainT A z v i j = 0) ∧
    (∀ r ≤ k, chainT A z v (k - r) (k + r) = (-1 : ℂ) ^ (r + 1) * (s : ℂ) * Complex.I) ∧
    (∀ r m : ℕ, m ≤ r → r ≤ k → 1 < r →
      chainT A z v (k - r) (k + m) =
        (-1 : ℂ) ^ (r + 1) * (s : ℂ) * Complex.I / 2 *
          ((r + m : ℕ) : ℂ) * (Nat.factorial (r - 1) : ℂ) /
            ((Nat.factorial m : ℂ) * (Nat.factorial (r - m) : ℂ))) ∧
    (∀ i j : ℕ, chainT A z v i j = -star (chainT A z v j i)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
