-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_isotropic_star_joinability
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.isotropic_star_joinability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:57:34.515935+00:00
-- url     : https://prove2.me/theorems/18ceb009-02a4-4137-aef4-ae65876f9275
-- title:
--   Theorem III.6: star joining of isotropic states
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   Let $n\ge1$ and let $0<\phi_j\le d$ for $1\le j\le n$. A state of a central qudit and $n$ outer qudits with isotropic central-to-outer marginals $\rho_I(\phi_j)$ exists precisely when
--   $$\sum_{j=1}^n\phi_j\le d-1+\frac{(\sum_{j=1}^n\sqrt{\phi_j})^2}{n+d-1}.$$
--   This is the asymmetric isotropic star compatibility criterion.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 11, Theorem III.6: star joining of isotropic states

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Theorem III.6, PDF pp.10–11: strictly positive physical parameters, as stated;
the final prose index is n, matching both displayed sums. -/
theorem isotropic_star_joinability (d n : ℕ) (hd : 2 ≤ d) (hn : 0 < n)
    (phi : Fin n → ℝ) (hphi : ∀ j, 0 < phi j ∧ phi j ≤ d) :
    IsotropicStarJoinable d n phi ↔
      (∑ j, phi j) ≤ ((d : ℝ)-1) +
        (∑ j, Real.sqrt (phi j))^2/((n : ℝ)+(d : ℝ)-1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
