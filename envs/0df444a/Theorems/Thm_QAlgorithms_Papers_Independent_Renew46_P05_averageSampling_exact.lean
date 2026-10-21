-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P05_averageSampling_exact
-- name    : QAlgorithms.Papers.Independent.Renew46.P05.averageSampling_exact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:55:31.325985+00:00
-- url     : https://prove2.me/theorems/19ebb1b9-55ab-4401-87b3-8491634ee9de
-- title:
--   §3, Eq. (3), unnumbered: average sampling of one-generator HS subspaces
-- statement:
--   Let $d\ge1$ and let $\mathcal H=L^2(\mathbb R^d;\mathbb C)$ with Lebesgue measure. Write $\mathrm{HS}(\mathcal H)$ for the Hilbert–Schmidt operators, with first-linear pairing $\langle T,Q\rangle_{\mathrm{HS}}=\operatorname{tr}(TQ^*)$. Let $\Lambda=A\mathbb Z^{2d}$ be a full-rank phase-space lattice, and set $\alpha_z(T)=\pi(z)T\pi(z)^*$, where $\pi(x,\omega)f(t)=e^{2\pi i\omega\cdot t}f(t-x)$. Lattice Fourier series use $e^{2\pi i\sigma(\lambda,z)}$, where $\sigma((x,\omega),(x',\omega'))=\omega\cdot x'-\omega'\cdot x$, and normalized Haar measure on $\widehat\Lambda$.
--
--   Fix $S\in\mathrm{HS}(\mathcal H)$ whose lattice translates form a Riesz sequence, and let $V_S^2$ be their closed HS span. Each $T\in V_S^2$ has unique coefficients $c\in\ell^2(\Lambda)$ with $T=\sum_\lambda c(\lambda)\alpha_\lambda(S)$.
--
--   Fix any $Q\in\mathrm{HS}(\mathcal H)$, without requiring $Q\in V_S^2$. Define $s_T(\lambda)=\langle T,\alpha_\lambda(Q)\rangle_{\mathrm{HS}}$ and $q(\lambda)=\langle S,\alpha_\lambda(Q)\rangle_{\mathrm{HS}}=\langle a_S,T_\lambda a_Q\rangle_{L^2}$. Suppose $|\mathcal F_\sigma^\Lambda q|$ is essentially bounded above and bounded away from zero. Put $p=(\mathcal F_\sigma^\Lambda)^{-1}(1/\mathcal F_\sigma^\Lambda q)$.
--
--   There is a unique reconstruction generator $H\in V_S^2$ working for every $T\in V_S^2$, and its translates are a Riesz basis of $V_S^2$. Explicitly,
--   $$
--   H=\mathcal T_Sp=L_{\mathcal T_{a_S}p},\qquad
--   T=\sum_{\lambda\in\Lambda}s_T(\lambda)\alpha_\lambda(H).
--   $$
--   The series converges unconditionally in HS norm. Here $\mathcal T_S$ and $\mathcal T_{a_S}$ are coefficient synthesis in operator space and Weyl-symbol space, respectively, and $L$ is the Weyl transform defined by the cross-Wigner pairing.
--
--   This is the physical average-sampling formula, including its actual inverse-filter construction.
-- source:
--   Average sampling in certain subspaces of Hilbert-Schmidt operators on $L^2(\mathbb{R}^d)$, arXiv:2011.05871v2, PDF p. 8, §3, Eq. (3), unnumbered: average sampling of one-generator HS subspaces

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

/-- García, PDF pp.7–9, Eq.(3) with its continuation.
H=T_S p=L_(T_(a_S)p) uses the actual HS and symbol syntheses. The
correlation is also identified with the source's symbol pairing. -/
theorem averageSampling_exact {d : ℕ} (hd : 0 < d) (L : Lattice d)
    (S Q : SchrodingerOperator d) (hS : IsHS S) (hQ : IsHS Q)
    (hRiesz : IsHSRieszSequence (translatedGenerators L (fun _ : Fin 1 => S)))
    (hStable : SamplingStable (singleMatrix (physicalKernel L S Q))) :
    let H := synthesize L (fun _ : Fin 1 => S) (fun _ => inverseFilter (physicalKernel L S Q))
    AverageReconstructs L S Q H ∧
    IsHSRieszBasisFor (samplingSpace L (fun _ : Fin 1 => S)) (translatedGenerators L (fun _ : Fin 1 => H)) ∧
    (∀ K : SchrodingerOperator d, AverageReconstructs L S Q K → K = H) ∧
    (let h := symbolSynthesis L (fun _ : Fin 1 => S) (fun _ => inverseFilter (physicalKernel L S Q))
     weylSymbol H = h ∧ H = weylOperator h) ∧
    (∀ k : LatticeIndex d,
      physicalKernel L S Q k =
        inner ℂ (translateSymbol (latticePoint L k) (weylSymbol Q)) (weylSymbol S)) ∧
    (∀ᵐ t ∂(volume : Measure (DualTorus d)),
      latticeFourier (inverseFilter (physicalKernel L S Q)) t = (latticeFourier (physicalKernel L S Q) t)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P05

end
