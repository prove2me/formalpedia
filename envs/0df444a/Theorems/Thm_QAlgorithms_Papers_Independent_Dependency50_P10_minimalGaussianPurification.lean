-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P10_minimalGaussianPurification
-- name    : QAlgorithms.Papers.Independent.Dependency50.P10.minimalGaussianPurification
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:08:11.390807+00:00
-- url     : https://prove2.me/theorems/c2be2d9b-ef9d-46e1-910f-bd11eee60b7f
-- title:
--   Attained minimal Gaussian purification and its explicit covariance construction
-- statement:
--   Let $G$ be the real symmetric covariance of a normalized $n$-mode Gaussian state, with $G-i\sigma_n\succeq0$ and $\sigma_n=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$. There exist a symplectic real matrix $S$ and $n$ numbers $d_j\ge1$ such that $SGS^T=H:=\operatorname{diag}(D,D)$, where $D=\operatorname{diag}(d_1,\ldots,d_n)$. Define $f(d)=-\sqrt{d^2-1}$, $\eta=\operatorname{diag}(f(d_j))$, $C=\begin{pmatrix}0&\eta\\\eta&0\end{pmatrix}$, and $c=\#\{j:d_j=1\}$. The explicit covariance
--
--   $$
--   \Gamma=\begin{pmatrix}H&C\\C^T&H\end{pmatrix}
--   $$
--
--   is physical and pure for $\sigma_n\oplus\sigma_n$. The original state has a Gaussian purification with exactly $q=n-c$ ancillary modes, and every Gaussian purification has at least $q$ ancillary modes. Moreover,
--
--   $$
--   c=n-\tfrac12\operatorname{rank}_{\mathbb C}(G-\sigma_nG^{-1}\sigma_n^T),\qquad
--   q=\operatorname{rank}_{\mathbb C}(G-i\sigma_n)-n,\qquad
--   2q=\operatorname{rank}_{\mathbb C}(G-\sigma_nG^{-1}\sigma_n^T).
--   $$
--
--   The inverse of $G$ is ordinary because a physical covariance is positive definite. Arbitrary first moments are accommodated by local displacements. The explicit $\Gamma$ initially uses $n$ ancillary modes; the attained minimum follows after ancillary vacuum modes are removed. The restriction to Gaussian purifications is essential.
-- source:
--   The optimal unitary dilation for bosonic Gaussian channels, arXiv:1009.1108v1, PDF p. 8, Appendix B.1, Eqs.(B2)–(B6), continuing on p.9

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P10

/-- Appendix B.1, PDF pp.8–9, Eqs.(B2)–(B6), plus the rank expression used
in PDF p.4, Eq.(22). Williamson data are constructed. The stated `n`-ancilla
block covariance is pure; removing ancillary vacuum modes attains the minimum
`n - #1(D)`, with a lower bound against every Gaussian purification.
The inverse in (B5) is ordinary: physical covariances are positive definite.
Arbitrary first moments can be supplied by local displacements. -/
theorem minimalGaussianPurification {n : ℕ}
    (G : Matrix (Phase n) (Phase n) ℝ)
    (hG : physicalCovariance G (sigma n)) :
    ∃ D : Fin n → ℝ,
      ∃ S : Matrix (Phase n) (Phase n) ℝ,
        (∀ j, 1 ≤ D j) ∧
        S * sigma n * S.transpose = sigma n ∧
        S * G * S.transpose = thermalCovariance D ∧
        pureCovariance (thermalPurification D) (jointSigma n n) ∧
        (unitCount D = n -
          (complexify (G - sigma n * G⁻¹ * (sigma n).transpose)).rank / 2) ∧
        hasGaussianPurification G (n - unitCount D) ∧
        (∀ q : ℕ, hasGaussianPurification G q → n - unitCount D ≤ q) ∧
        (n - unitCount D =
          (complexify G - Complex.I • complexify (sigma n)).rank - n) ∧
        (2 * (n - unitCount D) =
          (complexify (G - sigma n * G⁻¹ * (sigma n).transpose)).rank) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P10

end
