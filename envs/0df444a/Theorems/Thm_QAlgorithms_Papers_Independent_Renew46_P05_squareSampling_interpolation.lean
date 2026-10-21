-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P05_squareSampling_interpolation
-- name    : QAlgorithms.Papers.Independent.Renew46.P05.squareSampling_interpolation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:59:12.424324+00:00
-- url     : https://prove2.me/theorems/51f3e1fe-2234-4d65-93f8-f54c4c15f99a
-- title:
--   Corollary 3: square-system equivalence, uniqueness and interpolation
-- statement:
--   Let $d\ge1$ and let $\mathcal H=L^2(\mathbb R^d;\mathbb C)$ with Lebesgue measure. Write $\mathrm{HS}(\mathcal H)$ for the Hilbert–Schmidt operators, with first-linear pairing $\langle T,Q\rangle_{\mathrm{HS}}=\operatorname{tr}(TQ^*)$. Let $\Lambda=A\mathbb Z^{2d}$ be a full-rank phase-space lattice, and set $\alpha_z(T)=\pi(z)T\pi(z)^*$, where $\pi(x,\omega)f(t)=e^{2\pi i\omega\cdot t}f(t-x)$. Lattice Fourier series use $e^{2\pi i\sigma(\lambda,z)}$, where $\sigma((x,\omega),(x',\omega'))=\omega\cdot x'-\omega'\cdot x$, and normalized Haar measure on $\widehat\Lambda$.
--
--   Use the multigenerator setting with $N=M\ge1$, combined Riesz translates of the fixed HS generators $\mathbf S$, and their closed span $V_{\mathbf S}^2$. Let $\mathsf A$ be an $N\times N$ matrix with $\ell^2(\Lambda)$ entries, let $\widehat{\mathsf A}$ be its entrywise symplectic Fourier series, and define $s_T=\mathsf A*_\Lambda\mathbf c$ from the unique synthesis coefficients of $T$. Retain the section's standing bounded-system assumption $\beta_{\mathsf A}<\infty$; no positive lower bound is assumed.
--
--   The determinant condition
--   $$
--   0<\operatorname*{ess\,inf}_{\xi\in\widehat\Lambda}|\det\widehat{\mathsf A}(\xi)|
--   \le \operatorname*{ess\,sup}_{\xi\in\widehat\Lambda}|\det\widehat{\mathsf A}(\xi)|<\infty
--   $$
--   is equivalent to existence of a unique labelled tuple $(H_1,\ldots,H_N)\in(V_{\mathbf S}^2)^N$ whose translates form a Riesz basis and reconstruct every $T$ by
--   $$
--   T=\sum_{n=1}^N\sum_{\lambda\in\Lambda}s_{T,n}(\lambda)\alpha_\lambda(H_n)
--   $$
--   unconditionally in HS norm. Any tuple satisfying this reconstruction and basis property also has the interpolation property
--   $$
--   s_{H_n,n'}(\lambda)=\delta_{n,n'}\delta_{\lambda,0}.
--   $$
--
--   Thus a bounded square sampling system has unique interpolating reconstruction generators exactly when its determinant modulus stays away from zero.
-- source:
--   Average sampling in certain subspaces of Hilbert-Schmidt operators on $L^2(\mathbb{R}^d)$, arXiv:2011.05871v2, PDF p. 14, Corollary 3: square-system equivalence, uniqueness and interpolation

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P05

open Filter MeasureTheory

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Next46.P31 (EuclideanSchrodinger PhasePoint)

open QAlgorithms.Papers.Independent.Next46.P02 (hilbertSchmidtNorm)

open scoped BigOperators ENNReal Topology ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P05.unitCircleMeasureSpace

/-- García, PDF pp.14–15, Corollary 3. Ambient boundedness is taken from the
bounded-system context on pp.11–12 and the proof on p.15. Interpolation is
a conclusion. Determinant modulus bars were checked in the rendered PDF. -/
theorem squareSampling_interpolation {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (L : Lattice d) (S : Fin N → SchrodingerOperator d) (hS : ∀ n, IsHS (S n))
    (hRiesz : IsHSRieszSequence (translatedGenerators L S)) (A : SamplingMatrix d N N)
    (hUpper : UpperStable A) :
    (DeterminantStable A ↔ ∃! H : Fin N → SchrodingerOperator d,
      Reconstructs L S A H ∧ IsHSRieszBasisFor (samplingSpace L S) (translatedGenerators L H)) ∧
    (∀ H : Fin N → SchrodingerOperator d,
      Reconstructs L S A H → IsHSRieszBasisFor (samplingSpace L S) (translatedGenerators L H) →
      ∀ n nprime : Fin N, ∀ k : LatticeIndex d,
        samples A (coefficients L S (H n)) (nprime, k) =
          if n = nprime ∧ k = 0 then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P05

end
