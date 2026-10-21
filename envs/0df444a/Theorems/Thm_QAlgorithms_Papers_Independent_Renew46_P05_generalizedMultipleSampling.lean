-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P05_generalizedMultipleSampling
-- name    : QAlgorithms.Papers.Independent.Renew46.P05.generalizedMultipleSampling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:57:50.048846+00:00
-- url     : https://prove2.me/theorems/4ddd3edc-10f5-480b-9734-45b6320b3963
-- title:
--   Theorem 2: generalized multi-generator sampling, including converse
-- statement:
--   Let $d\ge1$ and let $\mathcal H=L^2(\mathbb R^d;\mathbb C)$ with Lebesgue measure. Write $\mathrm{HS}(\mathcal H)$ for the Hilbert–Schmidt operators, with first-linear pairing $\langle T,Q\rangle_{\mathrm{HS}}=\operatorname{tr}(TQ^*)$. Let $\Lambda=A\mathbb Z^{2d}$ be a full-rank phase-space lattice, and set $\alpha_z(T)=\pi(z)T\pi(z)^*$, where $\pi(x,\omega)f(t)=e^{2\pi i\omega\cdot t}f(t-x)$. Lattice Fourier series use $e^{2\pi i\sigma(\lambda,z)}$, where $\sigma((x,\omega),(x',\omega'))=\omega\cdot x'-\omega'\cdot x$, and normalized Haar measure on $\widehat\Lambda$.
--
--   Fix positive integers $N,M$ and $S_1,\ldots,S_N\in\mathrm{HS}(\mathcal H)$ whose combined lattice translates form a Riesz sequence. Let $V_{\mathbf S}^2$ be their closed HS span. Its elements have unique coefficients $\mathbf c=(c_n)_{n=1}^N\in\ell^2(\Lambda)^N$. For a fixed $M\times N$ matrix $\mathsf A=(a_{mn})$ with entries in $\ell^2(\Lambda)$, define $s_{T,m}=\sum_n a_{mn}*_\Lambda c_n$ and $\widehat{\mathsf A}=[\mathcal F_\sigma^\Lambda a_{mn}]$. Stability means there are $0<a\le b<\infty$ such that $a\|v\|_2^2\le\|\widehat{\mathsf A}(\xi)v\|_2^2\le b\|v\|_2^2$ for almost every $\xi$ and all $v\in\mathbb C^N$.
--
--   If the system is stable, then the supplied channel count necessarily satisfies $M\ge N$, and there is a fixed family $H_1,\ldots,H_M\in V_{\mathbf S}^2$ whose lattice translates form a frame for that space and such that every $T\in V_{\mathbf S}^2$ satisfies
--   $$
--   T=\sum_{m=1}^M\sum_{\lambda\in\Lambda}s_{T,m}(\lambda)\alpha_\lambda(H_m).
--   $$
--   Convergence is unconditional in HS norm over the combined channel/lattice index set.
--
--   Conversely, suppose only the finite essential upper spectral bound $\beta_{\mathsf A}<\infty$. If such a frame reconstruction holds for every $T$, then the positive essential lower bound $\alpha_{\mathsf A}>0$ follows.
--
--   This characterizes multichannel stable reconstruction while retaining the converse's weaker hypotheses.
-- source:
--   Average sampling in certain subspaces of Hilbert-Schmidt operators on $L^2(\mathbb{R}^d)$, arXiv:2011.05871v2, PDF p. 13, Theorem 2: generalized multi-generator sampling, including converse

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

/-- García, PDF pp.13–14, Theorem 2 with its converse on p.14.
The supplied M is fixed with A; M>=N is a conclusion, never a premise. -/
theorem generalizedMultipleSampling {d N M : ℕ} (hd : 0 < d) (hN : 0 < N) (hM : 0 < M)
    (L : Lattice d) (S : Fin N → SchrodingerOperator d) (hS : ∀ n, IsHS (S n))
    (hRiesz : IsHSRieszSequence (translatedGenerators L S)) (A : SamplingMatrix d M N) :
    (SamplingStable A → N ≤ M ∧ ∃ H : Fin M → SchrodingerOperator d,
      Reconstructs L S A H ∧ IsHSFrameFor (samplingSpace L S) (translatedGenerators L H)) ∧
    (UpperStable A → (∃ H : Fin M → SchrodingerOperator d,
      Reconstructs L S A H ∧ IsHSFrameFor (samplingSpace L S) (translatedGenerators L H)) → LowerStable A) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P05

end
