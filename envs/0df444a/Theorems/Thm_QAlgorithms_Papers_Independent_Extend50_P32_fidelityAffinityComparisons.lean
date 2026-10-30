-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_fidelityAffinityComparisons
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.fidelityAffinityComparisons
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:45:23.399981+00:00
-- url     : https://prove2.me/theorems/87a066d6-eb80-4cee-8022-4a3b6d554b5f
-- title:
--   Proposition 2.9: Fidelity-affinity comparisons
-- statement:
--   Let $\rho,\sigma$ be $d$-dimensional density matrices, $d\ge1$. Let $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ be root fidelity, $A(\rho,\sigma)=\operatorname{Tr}(\sqrt\rho\sqrt\sigma)$ be affinity, and $D_{H^2}(\rho,\sigma)=\operatorname{Tr}((\sqrt\rho-\sqrt\sigma)^2)$. The parameter $\epsilon$ denotes the indicated Hellinger-squared loss.
--
--   $$
--   F(\rho,\sigma)^2\le A(\rho,\sigma)\le F(\rho,\sigma),\qquad D_{H^2}(\rho,\sigma)=\epsilon\ \Longrightarrow\ 1-\epsilon/2\le F(\rho,\sigma).
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 13, Proposition 2.9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P32

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Matrix ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Extend50.P32

open QAlgorithms.Papers.Independent.Support50.P38 (wordMass tv)

-- For the density matrices below, the characteristic-polynomial identity
-- preserves all eigenvalues with multiplicity and is equivalent to unitary
-- diagonalization with these real eigenvalues. No accuracy is assumed.

open QAlgorithms.Papers.Independent.Gap20.P17 (HasSpectrum)

/-- Proposition 2.9, PDF p.13: F is ROOT fidelity. The lower comparison is
credited to ANSV08 Eqs.(28),(32); both comparisons and the consequence are retained. -/
theorem fidelityAffinityComparisons {d : ℕ} (hd : 0 < d)
    (rho sigma : Matrix (Fin d) (Fin d) ℂ)
    (hRho : IsDensityMatrix rho) (hSigma : IsDensityMatrix sigma) :
    rootFidelity rho sigma ^ 2 ≤ affinity rho sigma ∧
    affinity rho sigma ≤ rootFidelity rho sigma ∧
    ∀ epsilon : ℝ, quantumH2 rho sigma = epsilon → 1 - epsilon / 2 ≤ rootFidelity rho sigma := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
