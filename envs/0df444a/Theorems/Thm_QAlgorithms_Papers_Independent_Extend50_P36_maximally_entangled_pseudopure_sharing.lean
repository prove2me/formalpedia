-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_maximally_entangled_pseudopure_sharing
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.maximally_entangled_pseudopure_sharing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:11:35.259275+00:00
-- url     : https://prove2.me/theorems/a69ced08-07b4-431a-a5d8-21a898cf3b8d
-- title:
--   Sec. IV B, unnumbered: maximally entangled qubit mixtures have the same sharing properties
-- statement:
--   For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   Let $v$ be a normalized maximally entangled two-qubit vector, characterized by $\operatorname{Tr}_R|v\rangle\langle v|=I/2$, and let $0\le t\le1$. Put $\sigma_t=t|v\rangle\langle v|+(1-t)I/4$. For every positive $m,n$,
--   $$\sigma_t\text{ is }m\text{-}n\text{ sharable}\ \Longleftrightarrow\ \rho_W((1-3t)/2)\text{ is }m\text{-}n\text{ sharable}\ \Longleftrightarrow\ \rho_I((1+3t)/2)\text{ is }m\text{-}n\text{ sharable}.$$
--   The same mixing weight is used for both qubit families.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 13, Sec. IV B, unnumbered: maximally entangled qubit mixtures have the same sharing properties

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.IV B, PDF p.13: every maximally entangled pure qubit state, mixed with
identity at the same weight t, has exactly the Werner/isotropic sharing criteria. -/
theorem maximally_entangled_pseudopure_sharing
    (v : EuclideanSpace ℂ (Fin 2 × Fin 2)) (hv : ‖v‖ = 1)
    (hent : traceRight (pureDensity v) = fullyMixed (Fin 2))
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (Sharable m n (pseudoPure t v) ↔ Sharable m n (wernerSwapState 2 ((1-3*t)/2))) ∧
    (Sharable m n (pseudoPure t v) ↔ Sharable m n (isotropicOverlapState 2 ((1+3*t)/2))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
