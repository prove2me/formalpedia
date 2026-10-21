-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P05_generalizedSingleSampling
-- name    : QAlgorithms.Papers.Independent.Renew46.P05.generalizedSingleSampling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:56:50.928207+00:00
-- url     : https://prove2.me/theorems/e3eea8f2-10f1-424f-ae29-32fc50434483
-- title:
--   Theorem 1: generalized single-generator sampling, including converse
-- statement:
--   Let $d\ge1$ and let $\mathcal H=L^2(\mathbb R^d;\mathbb C)$ with Lebesgue measure. Write $\mathrm{HS}(\mathcal H)$ for the Hilbert–Schmidt operators, with first-linear pairing $\langle T,Q\rangle_{\mathrm{HS}}=\operatorname{tr}(TQ^*)$. Let $\Lambda=A\mathbb Z^{2d}$ be a full-rank phase-space lattice, and set $\alpha_z(T)=\pi(z)T\pi(z)^*$, where $\pi(x,\omega)f(t)=e^{2\pi i\omega\cdot t}f(t-x)$. Lattice Fourier series use $e^{2\pi i\sigma(\lambda,z)}$, where $\sigma((x,\omega),(x',\omega'))=\omega\cdot x'-\omega'\cdot x$, and normalized Haar measure on $\widehat\Lambda$.
--
--   Fix $S\in\mathrm{HS}(\mathcal H)$ whose lattice translates form a Riesz sequence, and let $V_S^2$ be their closed HS span. Each $T\in V_S^2$ has unique coefficients $c\in\ell^2(\Lambda)$ with $T=\sum_\lambda c(\lambda)\alpha_\lambda(S)$.
--
--   Let $q\in\ell^2(\Lambda)$ be arbitrary and define $s_T=c*_\Lambda q$ using the unique coefficients of $T$. If
--   $$
--   0<\operatorname*{ess\,inf}_{\xi\in\widehat\Lambda}|\mathcal F_\sigma^\Lambda q(\xi)|
--   \le \operatorname*{ess\,sup}_{\xi\in\widehat\Lambda}|\mathcal F_\sigma^\Lambda q(\xi)|<\infty,
--   $$
--   there is a unique $H\in V_S^2$ such that, for every $T\in V_S^2$,
--   $$
--   T=\sum_{\lambda\in\Lambda}(c*_\Lambda q)(\lambda)\alpha_\lambda(H)
--   $$
--   unconditionally in HS norm. The translates of $H$ form a Riesz basis for $V_S^2$.
--
--   Conversely, if a generator $H\in V_S^2$ has Riesz translates forming a basis for $V_S^2$ and this formula holds for every $T$, then the displayed Fourier bounds hold. No stability hypothesis is assumed for this converse, and $q$ need not come from an averaging operator.
--
--   This extends physical averages to arbitrary stable scalar convolution sampling.
-- source:
--   Average sampling in certain subspaces of Hilbert-Schmidt operators on $L^2(\mathbb{R}^d)$, arXiv:2011.05871v2, PDF p. 9, Theorem 1: generalized single-generator sampling, including converse

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

/-- García, PDF p.9, Theorem 1 in BOTH directions. Stability is the forward
antecedent only; the converse starts with the Riesz reconstruction formula. -/
theorem generalizedSingleSampling {d : ℕ} (hd : 0 < d) (L : Lattice d)
    (S : SchrodingerOperator d) (hS : IsHS S)
    (hRiesz : IsHSRieszSequence (translatedGenerators L (fun _ : Fin 1 => S))) (q : LatticeL2 d) :
    (SamplingStable (singleMatrix q) →
      ∃ H : SchrodingerOperator d,
        Reconstructs L (fun _ : Fin 1 => S) (singleMatrix q) (fun _ => H) ∧
        IsHSRieszBasisFor (samplingSpace L (fun _ : Fin 1 => S)) (translatedGenerators L (fun _ : Fin 1 => H)) ∧
        ∀ K : SchrodingerOperator d,
          Reconstructs L (fun _ : Fin 1 => S) (singleMatrix q) (fun _ => K) → K = H) ∧
    ((∃ H : SchrodingerOperator d,
      Reconstructs L (fun _ : Fin 1 => S) (singleMatrix q) (fun _ => H) ∧
      IsHSRieszBasisFor (samplingSpace L (fun _ : Fin 1 => S)) (translatedGenerators L (fun _ : Fin 1 => H))) →
        SamplingStable (singleMatrix q)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P05

end
