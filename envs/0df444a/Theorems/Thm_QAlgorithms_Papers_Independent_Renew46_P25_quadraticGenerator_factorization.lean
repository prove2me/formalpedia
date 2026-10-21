-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P25_quadraticGenerator_factorization
-- name    : QAlgorithms.Papers.Independent.Renew46.P25.quadraticGenerator_factorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:40:32.167509+00:00
-- url     : https://prove2.me/theorems/00b6acb3-6742-423c-8ee6-7ac9a918d766
-- title:
--   Factorization of quadratic Fourier generators
-- statement:
--   Let $n\ge1$, let $P,Q$ be real symmetric $n\times n$ matrices, and let $L$ be invertible. Let $m\in\mathbb Z$ satisfy $e^{i\pi m}=\operatorname{sgn}(\det L)$, allowing both choices modulo $4$. Set
--
--   $$W(x,y)=\tfrac12(Px)\cdot x-(Lx)\cdot y+\tfrac12(Qy)\cdot y,\qquad c_n=(2\pi)^{-n/2}e^{-i\pi n/4}.$$
--
--   Define $\widehat S_{W,m}f(x)=c_ni^m\sqrt{|\det L|}\int e^{iW(x,y)}f(y)\,dy$, $\widehat V_Pf(x)=e^{-i(Px)\cdot x/2}f(x)$, $\widehat M_{L,m}f(x)=i^m\sqrt{|\det L|}f(Lx)$ and $\widehat Jf(x)=c_n\int e^{-ix\cdot y}f(y)\,dy$. On Schwartz functions, and for the unitary extensions of these operators to Lebesgue $L^2(\mathbb R^n)$,
--
--   $$\widehat S_{W,m}=\widehat V_{-P}\widehat M_{L,m}\widehat J\widehat V_{-Q}.$$
--
--   This factorization does not require $\det(S_W-I)\ne0$.
--
--   **Formalization Note** The positive sign in the quadratic kernel follows (46) and p.28; p.21 prints a negative sign. The correction is disclosed for independent moderation. Existence of all L2 extensions is a conclusion.
-- source:
--   A Weyl Calculus on Symplectic Phase Space, arXiv:math-ph/0508024v2, PDF p. 22, Unnumbered (46): factorization of quadratic Fourier generators

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25

noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

namespace QAlgorithms.Papers.Independent.Renew46.P25

/-- PDF pp.21-22, (46), with the positive kernel sign actually used on p.28.
Printed/changed/why are recorded on quadraticGenerator and in MODERATION_NOTES.
The equality holds on Schwartz functions and for their unitary L2 extensions.
Neither the generators nor this theorem require det(S_W-I) nonzero. -/
theorem quadraticGenerator_factorization (n : ℕ) (hn : 0 < n)
    (P L Q : Matrix (Fin n) (Fin n) ℝ) (m : ℤ)
    (hP : P.IsSymm) (hQ : Q.IsSymm) (hL : L.det ≠ 0)
    (hm : admissiblePhase L m) :
    (∀ f : SchwartzMap (ConfigurationEuclidean n) ℂ,
      quadraticGenerator P L Q m f =
        quadraticChirp (-P) (quadraticDilation L m
          (quadraticFourier (quadraticChirp (-Q) f)))) ∧
    ∃ (U V M J R : ConfigurationEuclideanL2 n ≃ₗᵢ[ℂ] ConfigurationEuclideanL2 n),
      realizesConfiguration (quadraticGenerator P L Q m) U ∧
      realizesConfiguration (quadraticChirp (-P)) V ∧
      realizesConfiguration (quadraticDilation L m) M ∧
      realizesConfiguration quadraticFourier J ∧
      realizesConfiguration (quadraticChirp (-Q)) R ∧
      ∀ f, U f = V (M (J (R f))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P25

end
