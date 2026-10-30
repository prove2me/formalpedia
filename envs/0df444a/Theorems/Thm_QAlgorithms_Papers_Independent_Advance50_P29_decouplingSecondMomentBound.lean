-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_decouplingSecondMomentBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.decouplingSecondMomentBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:08:04.712505+00:00
-- url     : https://prove2.me/theorems/4e2aa99a-bb41-4068-8437-f4b8a5364d53
-- title:
--   §5, (23): upper bound on the averaged squared Frobenius defect
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. Let $\mathcal N:B(Q)\to B(Q^{\prime})$ be completely positive and trace nonincreasing, with a minimal finite Kraus family $(A_i)$ satisfying $\sum_i A_i^\dagger A_i\le I$. The family may be empty and the operation may be zero. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. Fix any $K$-dimensional seed code $C_0$ and average $C=UC_0$ over normalized Haar measure on the entire unitary group of $Q$; denote this expectation by $[\,\cdot\,]_K$. All displayed Haar integrands are integrable. For the supplied family $(A_i)_{i\in L}$ define $W_{ij}=A_i^\dagger A_j$ and the operator on $Q\otimes\mathbb C^L$
--   $$
--   D_C=K\sum_{i,j\in L}\left(\pi_CW_{ij}\pi_C-\operatorname{tr}(\pi_CW_{ij}\pi_C)\pi_C\right)\otimes|i\rangle\langle j|.
--   $$
--   Write $\|X\|_{\rm tr}=\operatorname{tr}\sqrt{X^\dagger X}$ and $\|X\|_F^2=\operatorname{tr}(X^\dagger X)$. The supplied family is minimal, as fixed after (15). Then
--
--   $$
--   [\|D_C\|_F^2]_K\le\|\mathcal N(\pi)\|_F^2.
--   $$
--
--   The simple second-moment bound is the interface used in deriving the fidelity estimate.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 13, §5, (23): upper bound on the averaged squared Frobenius defect

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF p.13, (23): second-moment bound for the minimal Kraus family fixed after (15). -/
theorem decouplingSecondMomentBound [Nonempty I] [Nonempty J]
    (A : L → Matrix J I ℂ) (hA : KrausTraceBound A) (hm : MinimalKraus A)
    (C : CodeProjection I) :
    Integrable (fun U => frobeniusSq (decoupling A C.dimension (rotatedDensity C U)))
      (Schur.unitaryHaar (Fintype.card I)) ∧
    codeAverage C (fun rho => frobeniusSq (decoupling A C.dimension rho)) ≤
      frobeniusSq (krausApply A (mixed I)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
