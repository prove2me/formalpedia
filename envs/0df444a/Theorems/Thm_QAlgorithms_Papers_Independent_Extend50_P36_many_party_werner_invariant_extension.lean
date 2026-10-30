-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_many_party_werner_invariant_extension
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.many_party_werner_invariant_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:09:31.329285+00:00
-- url     : https://prove2.me/theorems/97964cc1-6ab9-490b-8db9-9c4418802739
-- title:
--   Sec. IV A, unnumbered: invariant search space for N-party Werner joining
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.
--
--   Fix an integer $N\ge0$ and physical parameters $\psi_{ij}\in[-1,1]$ for distinct sites $i,j$. If a density operator on $(\mathbb C^d)^{\otimes N}$ has pair marginals $\rho_W(\psi_{ij})$, there is one with exactly the same pair marginals satisfying
--   $$U^{\otimes N}w(U^{\otimes N})^\dagger=w\qquad\text{for every }U\in U(d).$$
--   This restricts the extension search to the collective-invariant physical space, without any runtime or arbitrary mixed-tower decomposition assertion.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 12, Sec. IV A, unnumbered: invariant search space for N-party Werner joining

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.IV A, PDF p.12: a collectively invariant joining state exists whenever
all prescribed pair marginals are Werner and some joining state exists. -/
theorem many_party_werner_invariant_extension (d N : ℕ) (hd : 2 ≤ d)
    (psi : Fin N → Fin N → ℝ) (hpsi : ∀ i j, i ≠ j → -1 ≤ psi i j ∧ psi i j ≤ 1)
    (hjoin : ∃ X : Op (Fin N → Fin d), IsDensityMatrix X ∧
      ∀ i j, i ≠ j → pairMarginal X i j = wernerSwapState d (psi i j)) :
    ∃ X : Op (Fin N → Fin d), IsDensityMatrix X ∧
      (∀ i j, i ≠ j → pairMarginal X i j = wernerSwapState d (psi i j)) ∧
      ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        collectiveTensorOperator false (U : Op (Fin d)) * X * (collectiveTensorOperator false (U : Op (Fin d)))ᴴ = X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
