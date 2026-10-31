-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_pairing_recursion_and_terminal_identities
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.pairing_recursion_and_terminal_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:05:45.934569+00:00
-- url     : https://prove2.me/theorems/a32f788d-d58a-4d79-9a5f-4042ad7da0b3
-- title:
--   Lemma 6 — pairing recursion and terminal-chain identities
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For $\lambda\ne0$, $v,w\in V_{\mathbb C}$, $i\ge0$ and $j>0$,
--   $$\Omega_{\mathbb C}(N_\lambda^iv,N_{\lambda^{-1}}^jw)=-\lambda^{-1}\Omega_{\mathbb C}(N_\lambda^{i+1}v,N_{\lambda^{-1}}^jw)-\lambda^{-2}\Omega_{\mathbb C}(N_\lambda^{i+1}v,N_{\lambda^{-1}}^{j-1}w).$$
--   If $v\in E_\lambda$ has height $p$, meaning $N_\lambda^pv\ne0$ and $N_\lambda^{p+1}v=0$, then for $k,j\ge0$ with $j\le p+k$,
--   $$\Omega_{\mathbb C}(N_\lambda^{p+k}v,w)=(-\lambda^2)^j\Omega_{\mathbb C}(N_\lambda^{p+k-j}v,N_{\lambda^{-1}}^jw).$$
--   In particular,
--   $$\Omega_{\mathbb C}(N_\lambda^pv,w)=(-\lambda^2)^p\Omega_{\mathbb C}(v,N_{\lambda^{-1}}^pw),\qquad \Omega_{\mathbb C}(N_\lambda^kv,N_{\lambda^{-1}}^jw)=0\text{ if }k+j>p.$$
--   The restriction $j\le p+k$ corrects the undefined negative exponents in printed (12); it does not truncate them to zero.
--
--
--   These are all four terminal-chain identities, with the source formula stated on its defined domain.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 9, Lemma 6 — pairing recursion and terminal-chain identities

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

/-- PDF p.9, Lemma 6, (11)–(14). Printed: (12) permits arbitrary j.
Changed: j<=p+k in (12), so its exponent is nonnegative. Why: negative powers
of the singular shifted map are undefined; Nat subtraction must not hide this.
The proof's p versus p+1 nilpotence typo is resolved using VectorHeight. -/
theorem pairing_recursion_and_terminal_identities {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz : z ≠ 0) :
    (∀ (v w : CVec n) (i j : ℕ), 0 < j →
      omegaC ((shifted A z ^ i) v) ((shifted A z⁻¹ ^ j) w) =
        -z⁻¹ * omegaC ((shifted A z ^ (i + 1)) v) ((shifted A z⁻¹ ^ j) w) -
        (z ^ 2)⁻¹ * omegaC ((shifted A z ^ (i + 1)) v) ((shifted A z⁻¹ ^ (j - 1)) w)) ∧
    (∀ (v w : CVec n) (p : ℕ), v ∈ generalizedSpace A z → VectorHeight A z v p →
      (∀ k j : ℕ, j ≤ p + k → omegaC ((shifted A z ^ (p + k)) v) w =
        (-(z ^ 2)) ^ j * omegaC ((shifted A z ^ (p + k - j)) v) ((shifted A z⁻¹ ^ j) w)) ∧
      omegaC ((shifted A z ^ p) v) w =
        (-(z ^ 2)) ^ p * omegaC v ((shifted A z⁻¹ ^ p) w) ∧
      (∀ k j : ℕ, p < k + j →
        omegaC ((shifted A z ^ k) v) ((shifted A z⁻¹ ^ j) w) = 0)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
