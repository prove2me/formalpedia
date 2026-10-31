-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_universal_state
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.universal_state
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:22:43.364974+00:00
-- url     : https://prove2.me/theorems/0273a24a-f6bc-4def-9204-fad1b707b190
-- title:
--   Lemma 1: Universal permutation-invariant state
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. Let $d=|A|\ge1$ and $n\ge0$. Let $U_\pi$ permute the $n$ tensor factors and define the specific state from (2.7) by $\omega_n=(g_{n,d}n!)^{-1}\sum_{\pi\in S_n}\operatorname{tr}(U_\pi)U_\pi$. Then $\omega_n$ is a density operator and every permutation invariant density $\tau_n$ satisfies
--   $$\tau_n\le g_{n,d}\omega_n,\qquad g_{n,d}=\binom{n+d^2-1}{n}\le(n+1)^{d^2-1}.$$
--   Moreover, for the Young diagrams $\Lambda_{n,d}$ of size $n$ and height at most $d$, there is a probability vector $(p_\lambda)$ with
--   $$\omega_n=\sum_{\lambda\in\Lambda_{n,d}}p_\lambda\frac{P_\lambda}{\operatorname{tr}P_\lambda},\qquad |\Lambda_{n,d}|\le(n+1)^{d-1}.$$
--   Here the canonical full isotypic projectors $P_\lambda$ are nonzero mutually orthogonal projections. The state is invariant under permutations and every $U^{\otimes n}$ and commutes with every permutation invariant state.
--
--   This is the universal reference used in the classical representations and tests. At $n=0$ the register is one dimensional, $g_{0,d}=1$, and $\omega_0=1$.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 5, Lemma 1: Universal permutation-invariant state

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF pp.5--6, Lemma 1, all three clauses.
The state is computed by (2.7), not an arbitrary dominating family. The zero-fold
register is one-dimensional; d is strictly positive. -/
theorem universal_state (d : ℕ) (hd : 0 < d) (n : ℕ) :
    IsDensityMatrix (universal n d) ∧
    (∀ tau : Op (Fin n → Fin d), IsDensityMatrix tau → StatePermutationInvariant n d tau →
      (((universalFactor n d : ℕ) : ℂ) • universal n d - tau).PosSemidef) ∧
    universalFactor n d ≤ (n+1)^(d*d-1) ∧
    (∃ p : Schur.Partition d n → ℝ,
      (∀ l, 0 ≤ p l) ∧ (∑ l, p l) = 1 ∧
      universal n d = ∑ l, ((p l : ℂ) / (Schur.isotypicProjector l).trace) • Schur.isotypicProjector l) ∧
    (∀ l : Schur.Partition d n,
      (Schur.isotypicProjector l)ᴴ = Schur.isotypicProjector l ∧
      Schur.isotypicProjector l * Schur.isotypicProjector l = Schur.isotypicProjector l ∧
      0 < (Schur.isotypicProjector l).trace.re) ∧
    (∀ l k : Schur.Partition d n, l ≠ k → Schur.isotypicProjector l * Schur.isotypicProjector k = 0) ∧
    Fintype.card (Schur.Partition d n) ≤ (n+1)^(d-1) ∧
    StatePermutationInvariant n d (universal n d) ∧
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      copies n (U : Op (Fin d)) * universal n d * (copies n (U : Op (Fin d)))ᴴ = universal n d) ∧
    (∀ tau : Op (Fin n → Fin d), IsDensityMatrix tau → StatePermutationInvariant n d tau →
      universal n d * tau = tau * universal n d) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
