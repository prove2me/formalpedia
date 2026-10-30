-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_symmetric_star_concurrence_sums
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.symmetric_star_concurrence_sums
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:07:17.862989+00:00
-- url     : https://prove2.me/theorems/32e48f0e-c672-477a-b5ca-fb6d72455757
-- title:
--   Sec. III E, unnumbered: symmetric star concurrence sums
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   Let $n\ge1$. A central qudit having the same Werner state with each of its $n$ neighbors satisfies $nC_W(\psi)\le d-1$, where $C_W(\psi)=\max(0,-\psi)$. For identical isotropic marginals, $C_I(\phi)=\sqrt{2/(d(d-1))}\max(0,\phi-1)$ and
--   $$nC_I(\phi)\le\sqrt{2(d-1)/d}.$$
--   Both conclusions assume existence of the corresponding star sharing state; they are not asserted for arbitrary asymmetric marginals.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 11, Sec. III E, unnumbered: symmetric star concurrence sums

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.III E, PDF p.11: the linear concurrence rules require identical central
marginals, expressed by 1-n sharing, separately for the two families. -/
theorem symmetric_star_concurrence_sums (d n : ℕ) (hd : 2 ≤ d) (hn : 0 < n) :
    (∀ psi : ℝ, -1 ≤ psi → psi ≤ 1 → Sharable 1 n (wernerSwapState d psi) →
      (n : ℝ)*wernerConcurrence psi ≤ (d : ℝ)-1) ∧
    (∀ phi : ℝ, 0 ≤ phi → phi ≤ d → Sharable 1 n (isotropicOverlapState d phi) →
      (n : ℝ)*isotropicConcurrence d phi ≤ Real.sqrt (2*((d : ℝ)-1)/d)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
