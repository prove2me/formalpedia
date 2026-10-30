-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_qubit_werner_two_sided
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.qubit_werner_two_sided
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:10:17.994646+00:00
-- url     : https://prove2.me/theorems/9e0ab342-2e44-4382-ac82-c035a0722b2c
-- title:
--   Sec. IV B, unnumbered: Werner qubit 1-n sharing implies n-n sharing
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   For every $n\ge1$ and every qubit Werner parameter $\psi\in[-1,1]$,
--   $$\rho_W(\psi)\text{ is }1\text{-}n\text{ sharable}\quad\Longrightarrow\quad\rho_W(\psi)\text{ is }n\text{-}n\text{ sharable}.$$
--   This is the source's all-counts implication, distinct from its finite table.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 12, Sec. IV B, unnumbered: Werner qubit 1-n sharing implies n-n sharing

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.IV B, PDF p.12: the all-n qubit Werner implication, beyond the finite table. -/
theorem qubit_werner_two_sided (n : ℕ) (hn : 0 < n)
    (psi : ℝ) (hpsi : -1 ≤ psi ∧ psi ≤ 1) (hshare : Sharable 1 n (wernerSwapState 2 psi)) :
    Sharable n n (wernerSwapState 2 psi) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
