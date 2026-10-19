-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P07_gaussian_six_canonical_forms
-- name    : QAlgorithms.Papers.Independent.Frontier30.P07.gaussian_six_canonical_forms
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:36:05.797007+00:00
-- url     : https://prove2.me/theorems/d08f9af3-e9c0-4927-b111-7b8513f6b166
-- title:
--   Six canonical forms of one-mode Gaussian channels after displacement removal
-- statement:
--   Let $H$ be the full one-mode oscillator Hilbert space and let $V(z)$, $z=(x,y)\in\mathbb R^2$, be a regular irreducible Weyl representation with $\hbar=1$ and argument symplectic form $\Delta(z,w)=w_xz_y-z_xw_y$. Let $\Phi^*$ be a normal completely positive unital map on $B(H)$ with Gaussian action
--
--   $$
--   \Phi^*(V(z))=\exp[-\alpha(z,z)/2+i\ell(z)]V(Kz).
--   $$
--
--   Here $K$ and $\ell$ are real linear and $\alpha$ is a real symmetric bilinear form satisfying the finite-list positive-type condition (5). There is a displacement $V(s)$ that removes $\ell$, and there are symplectic transformations $T_1,T_2$ and canonical unitaries $U_1,U_2$ implementing them, such that
--
--   $$
--   K_0=T_1KT_2,\qquad a_0(z)=\alpha(T_2z,T_2z),
--   $$
--   $$
--   U_1^*\Phi^*\!\left(V(s)^*U_2^*V(z)U_2V(s)\right)U_1
--    =e^{-a_0(z)/2}V(K_0z).
--   $$
--
--   Writing $r^2=x^2+y^2$, the pair $(K_0z,a_0(z))$ is one of the following six forms:
--
--   $$
--   \begin{array}{c|c|c}
--   A_1&(0,0)&(N_0+\tfrac12)r^2\\
--   A_2&(x,0)&(N_0+\tfrac12)r^2\\
--   B_1&(x,y)&x^2/2\\
--   B_2&(x,y)&N_cr^2\\
--   C&(kx,ky)&|k^2-1|(N_0+\tfrac12)r^2\\
--   D&(kx,-ky)&(k^2+1)(N_0+\tfrac12)r^2.
--   \end{array}
--   $$
--
--   All thermal parameters $N_0$ and the classical-noise parameter $N_c$ are nonnegative. In case $C$, $k>0$ and $k\ne1$; in case $D$, $k>0$. The displayed linear maps identify the determinant and rank regimes in the source. No uniqueness of the parameters or canonical unitaries is asserted.
--
--   This classifies actual Gaussian channels under input and output canonical unitaries, with affine displacement removal performed first. In particular, the $B_1$ multiplier is the printed $e^{-x^2/4}$, and $B_2$ includes the identity endpoint $N_c=0$.
-- source:
--   One-mode quantum Gaussian channels, arXiv:quant-ph/0607051v2, PDF p. 2, §1, unnumbered Theorem, pp.2–4

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P07

noncomputable section

open Filter MeasureTheory

open scoped Topology ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Frontier30.P07

/-- Six canonical forms up to input/output canonical unitaries, after the
preliminary displacement removal: PDF pp.1–4, unnumbered Theorem, (3)–(5).
The conclusion gives the actual transformed Heisenberg action as well as
K'=T1 K T2 and alpha'(z,z)=alpha(T2z,T2z). The displayed K identities also
identify the determinant/rank cases of the source. No uniqueness is asserted.
-/
theorem gaussian_six_canonical_forms
    (W : WeylRepresentation) (Phi : NormalChannel)
    (K : PhaseSpace →ₗ[ℝ] PhaseSpace) (alpha : CovarianceForm)
    (mean : PhaseSpace →ₗ[ℝ] ℝ)
    (hnoise : AdmissibleNoise K alpha)
    (hgaussian : HasGaussianAction W Phi K alpha mean) :
    ∃ (shift : PhaseSpace) (T1 T2 : PhaseSpace ≃ₗ[ℝ] PhaseSpace)
      (U1 U2 : Observable) (form : CanonicalForm),
      IsSymplectic T1 ∧ IsSymplectic T2 ∧
      Implements W T1 U1 ∧ Implements W T2 U2 ∧ ValidCanonical form ∧
      (∀ z, Phi.action (star (W.operator shift) * W.operator z * W.operator shift) =
        Complex.exp (((-alpha z z / 2 : ℝ) : ℂ)) • W.operator (K z)) ∧
      (∀ z, T1 (K (T2 z)) = canonicalLinear form z) ∧
      (∀ z, alpha (T2 z) (T2 z) = canonicalNoise form z) ∧
      (∀ z, star U1 * Phi.action
        (star (W.operator shift) * (star U2 * W.operator z * U2) * W.operator shift) * U1 =
        Complex.exp (((-canonicalNoise form z / 2 : ℝ) : ℂ)) •
          W.operator (canonicalLinear form z)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P07

end
