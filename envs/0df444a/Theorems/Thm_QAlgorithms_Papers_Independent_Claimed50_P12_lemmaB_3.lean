-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:51:04.15577+00:00
-- url     : https://prove2.me/theorems/c84df38e-32fb-41ea-8ea7-c4b571ce7f65
-- title:
--   Uhlmann's overlap supremum
-- statement:
--   Let $D,R$ be nonzero finite-dimensional systems and $\rho,\sigma\ge0$ on $D$. Let $\psi,\phi\in D\otimes R$ be actual purifications, meaning $\operatorname{tr}_R|\psi\rangle\langle\psi|=\rho$ and $\operatorname{tr}_R|\phi\rangle\langle\phi|=\sigma$. Then
--
--   $$F(\rho,\sigma)=\sup_{U_R\ \mathrm{unitary}}\left|\langle\psi|(\mathrm{id}_D\otimes U_R)|\phi\rangle\right|.$$
--
--   The vectors may be unnormalized. The overlap has its complex absolute value and the identity acts on $D$.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 21, Lemma B.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma B.3, Eq.161 (PDF p.21): Uhlmann's supremum, with absolute overlap.
Purifications are actual vectors with the stated marginals, and may be unnormalized. -/
theorem lemmaB_3 {D R : Type*} [Fintype D] [Fintype R]
    [DecidableEq D] [DecidableEq R] [Nonempty D] [Nonempty R]
    (rho sigma : Op D) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (psi phi : D × R → ℂ) (hpsi : UnnormalizedPurifies psi rho) (hphi : UnnormalizedPurifies phi sigma) :
    rootFidelity rho sigma = sSup {v : ℝ | ∃ U : Matrix.unitaryGroup R ℂ,
      v = ‖∑ x : D × R, conj (psi x) *
        ∑ r : R, (U : Op R) x.2 r * phi (x.1,r)‖} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
