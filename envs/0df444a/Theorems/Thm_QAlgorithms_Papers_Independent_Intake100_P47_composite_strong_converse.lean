-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_composite_strong_converse
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.composite_strong_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:32:31.363384+00:00
-- url     : https://prove2.me/theorems/3b28a85d-fed7-43e0-8e54-2e029d7c9ba2
-- title:
--   Theorem 14: Exact strong converse exponent
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For a state $\rho_{AB}$ and a positive reference $\tau_A$ covering $\rho_A$, write $I_\alpha(\rho\|\tau)=\inf_{\sigma_B\in\mathcal S(B)}D_\alpha(\rho\|\tau\otimes\sigma_B)$ and $\widetilde I_\alpha$ for the analogous sandwiched quantity. For any block size $n$, let $\widehat\alpha_n(\mu;\rho,\tau)$ be the minimum rejection probability $\operatorname{tr}[(1-Q)\rho_{AB}^{\otimes n}]$ over all joint effects $0\le Q\le1$ satisfying $\sup_{\sigma_{B^n}\in\mathcal S(B^n)}\operatorname{tr}[Q(\tau_A^{\otimes n}\otimes\sigma_{B^n})]\le\mu$. The alternatives include every correlated block state. Limits run through positive integers and $-\log0=+\infty$. For states $\rho_{AB},\tau_A$ with $\rho_A\ll\tau_A$ and $0<R<\widetilde I_\infty(\rho\|\tau)$,
--   $$\lim_n-\frac1n\log\left[1-\widehat\alpha_n(e^{-nR};\rho,\tau)\right]=\sup_{s>1}\frac{s-1}{s}\left[R-\widetilde I_s(\rho\|\tau)\right].$$
--   In addition, the explicit converse bound (6.44), PDF p.19, holds for every $R>0$: the liminf of the left side is at least the displayed supremum. The exact limit retains its strict upper rate bound. This identifies the strong-converse exponent in the source's stated range.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 15, Theorem 14: Exact strong converse exponent

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

/-- arXiv:1408.6894v5, PDF p.15, Theorem 14, (6.1), and the explicit
all-positive-rate lower bound (6.44), PDF p.19. The exact limit retains the
strict upper rate bound; the second clause asserts only the liminf bound. -/
theorem composite_strong_converse [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : IsDensityMatrix tau) (hS : SupportLE (traceRight rho) tau) :
    (∀ R : ℝ, 0 < R → (R : EReal) < generalizedInformation true ⊤ rho tau →
      Tendsto (fun k : ℕ => normalizedErrorExponent (k+1) (1-exponentialCompositeError rho tau (k+1) R))
        atTop (𝓝 (strongValue rho tau R))) ∧
    (∀ R : ℝ, 0 < R → strongValue rho tau R ≤
      Filter.liminf (fun k : ℕ => normalizedErrorExponent (k+1) (1-exponentialCompositeError rho tau (k+1) R)) atTop) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
