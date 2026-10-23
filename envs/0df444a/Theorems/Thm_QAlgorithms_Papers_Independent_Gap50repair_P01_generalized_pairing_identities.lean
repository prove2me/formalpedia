-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_generalized_pairing_identities
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.generalized_pairing_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:20:06.389991+00:00
-- url     : https://prove2.me/theorems/8df36f8d-08cf-4c8a-a97f-a9e7b0bf60f5
-- title:
--   Lemma 22
-- statement:
--   Let $A$ be symplectic and $0\ne\lambda\in\mathbb C$. Put $L=A-\lambda I$ and $M=A-\lambda^{-1}I$ on the complexified space. For arbitrary $v,w$, $i\ge0$ and $j>0$,
--
--   $$\Omega_0(L^iv,M^jw)=-\lambda^{-1}\Omega_0(L^{i+1}v,M^jw)-\lambda^{-2}\Omega_0(L^{i+1}v,M^{j-1}w).$$
--
--   If $\lambda$ is an eigenvalue and $p$ is its maximal nonzero nilpotent height, then for $v,w\in E_\lambda$ and $k,j\ge0$ with $j\le p+k$, $\Omega_0(L^{p+k}v,w)=(-\lambda^2)^j\Omega_0(L^{p+k-j}v,M^jw)$. In particular $\Omega_0(L^pv,w)=(-\lambda^2)^p\Omega_0(v,M^pw)$, and $\Omega_0(L^kv,M^jw)=0$ if $k+j>p$. The guard on subtraction is supplied by the source's induction, and the printed $E_\lambda$ condition on both vectors is retained. These are all four technical identities.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 18, Lemma 22

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Lemma 22, PDF p.18. Printed (26) leaves the range of j unstated; use
j<=p+k, exactly the range in its proof, to keep p+k-j a nonnegative exponent.
All four formulas and both printed E_lambda premises are retained. -/
theorem generalized_pairing_identities {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz0 : z ≠ 0) :
    (∀ v w : Coord n → ℂ, ∀ i j : ℕ, 0 < j →
      omegaC ((shifted A z^i) v) ((shifted A z⁻¹^j) w) =
      -(1/z)*omegaC ((shifted A z^(i+1)) v) ((shifted A z⁻¹^j) w) -
      (1/z^2)*omegaC ((shifted A z^(i+1)) v) ((shifted A z⁻¹^(j-1)) w)) ∧
    (IsEigenvalue A z → ∀ p, HasNilpotentHeight A z p →
      ∀ v ∈ generalizedSpace A z, ∀ w ∈ generalizedSpace A z,
      (∀ k j : ℕ, j ≤ p+k → omegaC ((shifted A z^(p+k)) v) w =
        (-z^2)^j*omegaC ((shifted A z^(p+k-j)) v) ((shifted A z⁻¹^j) w)) ∧
      omegaC ((shifted A z^p) v) w = (-z^2)^p*omegaC v ((shifted A z⁻¹^p) w) ∧
      (∀ k j : ℕ, p < k+j → omegaC ((shifted A z^k) v) ((shifted A z⁻¹^j) w) = 0)) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
