-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_twirling_sharing_bounds
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.twirling_sharing_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:00:56.424989+00:00
-- url     : https://prove2.me/theorems/e9a72607-ccfd-40ab-ba7b-6a356258da92
-- title:
--   Corollary IV.2: twirling bounds arbitrary-state sharing
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   For any bipartite density operator $\rho$ and unitary $V\in U(d)$, put $\rho_V=(I\otimes V)\rho(I\otimes V)^\dagger$. With normalized Haar measure $\mu$ on $U(d)$ define
--   $$W=\int(U\otimes U)\rho_V(U\otimes U)^\dagger d\mu(U),\qquad T=\int(\overline U\otimes U)\rho_V(\overline U\otimes U)^\dagger d\mu(U).$$
--   Both outputs are density operators, with $W=\rho_W(\psi)$ for some $\psi\in[-1,1]$ and $T=\rho_I(\phi)$ for some $\phi\in[0,d]$. For each $m,n\ge1$,
--   $$\rho\text{ is }m\text{-}n\text{ sharable}\ \Longrightarrow\ W,T\text{ are }m\text{-}n\text{ sharable}.$$
--   This supplies necessary sharing conditions on arbitrary states.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 13, Corollary IV.2: twirling bounds arbitrary-state sharing

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Corollary IV.2, PDF p.13: the local rotation precedes each normalized Haar twirl;
no-more-sharable means an implication for each positive finite m,n. -/
theorem twirling_sharing_bounds (d : ℕ) (hd : 2 ≤ d)
    (rho : Op (Fin d × Fin d)) (hrho : IsDensityMatrix rho)
    (V : Matrix.unitaryGroup (Fin d) ℂ) :
    let rotated := localConjugate 1 (V : Op (Fin d)) rho
    let W := pairTwirl false rotated
    let T := pairTwirl true rotated
    (∃ psi : ℝ, -1 ≤ psi ∧ psi ≤ 1 ∧ W = wernerSwapState d psi) ∧
    (∃ phi : ℝ, 0 ≤ phi ∧ phi ≤ d ∧ T = isotropicOverlapState d phi) ∧
    IsDensityMatrix W ∧ IsDensityMatrix T ∧
    (∀ m n : ℕ, 0 < m → 0 < n → Sharable m n rho → Sharable m n W ∧ Sharable m n T) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
