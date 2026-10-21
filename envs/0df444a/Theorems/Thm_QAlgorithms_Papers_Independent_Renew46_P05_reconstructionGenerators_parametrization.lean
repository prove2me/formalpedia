-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P05_reconstructionGenerators_parametrization
-- name    : QAlgorithms.Papers.Independent.Renew46.P05.reconstructionGenerators_parametrization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:01:32.509536+00:00
-- url     : https://prove2.me/theorems/78ca909e-fff1-49e8-bc20-feb147a9e9df
-- title:
--   §4, unnumbered: construction and parametrization of reconstruction generators
-- statement:
--   Let $d\ge1$ and let $\mathcal H=L^2(\mathbb R^d;\mathbb C)$ with Lebesgue measure. Write $\mathrm{HS}(\mathcal H)$ for the Hilbert–Schmidt operators, with first-linear pairing $\langle T,Q\rangle_{\mathrm{HS}}=\operatorname{tr}(TQ^*)$. Let $\Lambda=A\mathbb Z^{2d}$ be a full-rank phase-space lattice, and set $\alpha_z(T)=\pi(z)T\pi(z)^*$, where $\pi(x,\omega)f(t)=e^{2\pi i\omega\cdot t}f(t-x)$. Lattice Fourier series use $e^{2\pi i\sigma(\lambda,z)}$, where $\sigma((x,\omega),(x',\omega'))=\omega\cdot x'-\omega'\cdot x$, and normalized Haar measure on $\widehat\Lambda$.
--
--   Fix positive integers $N,M$ and $S_1,\ldots,S_N\in\mathrm{HS}(\mathcal H)$ whose combined lattice translates form a Riesz sequence. Let $V_{\mathbf S}^2$ be their closed HS span. Its elements have unique coefficients $\mathbf c=(c_n)_{n=1}^N\in\ell^2(\Lambda)^N$. For a fixed $M\times N$ matrix $\mathsf A=(a_{mn})$ with entries in $\ell^2(\Lambda)$, define $s_{T,m}=\sum_n a_{mn}*_\Lambda c_n$ and $\widehat{\mathsf A}=[\mathcal F_\sigma^\Lambda a_{mn}]$. Stability means there are $0<a\le b<\infty$ such that $a\|v\|_2^2\le\|\widehat{\mathsf A}(\xi)v\|_2^2\le b\|v\|_2^2$ for almost every $\xi$ and all $v\in\mathbb C^N$.
--
--   Assume stability. For almost every $\xi$, write
--   $$
--   \widehat{\mathsf A}^{\dagger}
--   =(\widehat{\mathsf A}^*\widehat{\mathsf A})^{-1}\widehat{\mathsf A}^*,
--   \qquad
--   \widehat{\mathsf B}_C
--   =\widehat{\mathsf A}^{\dagger}
--   +C(I_M-\widehat{\mathsf A}\widehat{\mathsf A}^{\dagger}),
--   $$
--   where $C$ is any $N\times M$ measurable matrix function with essentially bounded entries. Every $\widehat{\mathsf B}_C$ is an essentially bounded left inverse, and every essentially bounded left inverse is of this form almost everywhere. No uniqueness of $C$ is asserted.
--
--   Take inverse lattice Fourier series columnwise to obtain $\mathbf b_m\in\ell^2(\Lambda)^N$, and construct
--   $$
--   H_m=\mathcal T_{\mathbf S}\mathbf b_m
--   =L_{\mathcal T_{\mathbf a_S}\mathbf b_m},\qquad
--   T=\sum_{m=1}^M\sum_{\lambda\in\Lambda}s_{T,m}(\lambda)\alpha_\lambda(H_m).
--   $$
--   The generators lie in $V_{\mathbf S}^2$, their translates form a frame, and the formula holds for every $T$ unconditionally in HS norm. Here the two synthesis maps use respectively the original operators and their actual Weyl symbols.
--
--   The choice $C=0$ gives the canonical pseudoinverse construction. Conversely every translated-generator frame reconstruction is obtained from a parameter $C$ as above. If $M>N$, infinitely many distinct labelled reconstruction families exist.
--
--   This describes all reconstruction choices and explicitly ties them to the original synthesis, rather than treating the generators as unrelated objects.
-- source:
--   Average sampling in certain subspaces of Hilbert-Schmidt operators on $L^2(\mathbb{R}^d)$, arXiv:2011.05871v2, PDF p. 14, §4, unnumbered: construction and parametrization of reconstruction generators

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

/-- García, PDF pp.12–14: constructed inverse-Fourier columns, all bounded
left inverses, canonical C=0, all frame reconstructions, and infinitely many
distinct reconstruction families for M>N. No injectivity in C is asserted. -/
theorem reconstructionGenerators_parametrization {d N M : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hM : 0 < M)
    (L : Lattice d) (S : Fin N → SchrodingerOperator d) (hS : ∀ n, IsHS (S n))
    (hRiesz : IsHSRieszSequence (translatedGenerators L S)) (A : SamplingMatrix d M N)
    (hStable : SamplingStable A) :
    (∀ C : DualTorus d → Matrix (Fin N) (Fin M) ℂ, BoundedTransfer C →
      BoundedTransfer (parametrizedInverse A C) ∧
      ConstructedWithSymbols L S (parametrizedInverse A C) ∧
      (∀ᵐ t ∂(volume : Measure (DualTorus d)), parametrizedInverse A C t * transfer A t = 1) ∧
      Reconstructs L S A (reconstructionFamily L S (parametrizedInverse A C)) ∧
      IsHSFrameFor (samplingSpace L S) (translatedGenerators L (reconstructionFamily L S (parametrizedInverse A C)))) ∧
    (BoundedTransfer (transferPseudoInverse A) ∧
      ConstructedWithSymbols L S (transferPseudoInverse A) ∧
      Reconstructs L S A (reconstructionFamily L S (transferPseudoInverse A)) ∧
      IsHSFrameFor (samplingSpace L S) (translatedGenerators L (reconstructionFamily L S (transferPseudoInverse A)))) ∧
    (∀ B : DualTorus d → Matrix (Fin N) (Fin M) ℂ, BoundedTransfer B →
      ((∀ᵐ t ∂(volume : Measure (DualTorus d)), B t * transfer A t = 1) ↔
        ∃ C : DualTorus d → Matrix (Fin N) (Fin M) ℂ,
          BoundedTransfer C ∧ (∀ᵐ t ∂(volume : Measure (DualTorus d)), B t = parametrizedInverse A C t))) ∧
    (∀ H : Fin M → SchrodingerOperator d,
      Reconstructs L S A H → IsHSFrameFor (samplingSpace L S) (translatedGenerators L H) →
      ∃ C : DualTorus d → Matrix (Fin N) (Fin M) ℂ,
        BoundedTransfer C ∧ H = reconstructionFamily L S (parametrizedInverse A C)) ∧
    (N < M → Set.Infinite {H : Fin M → SchrodingerOperator d |
      Reconstructs L S A H ∧ IsHSFrameFor (samplingSpace L S) (translatedGenerators L H)}) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P05

end
