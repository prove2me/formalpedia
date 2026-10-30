-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_table_qubit_thresholds
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.table_qubit_thresholds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:08:09.463148+00:00
-- url     : https://prove2.me/theorems/3b8e02cc-e750-4f4e-8523-f1256c54a1b7
-- title:
--   Table I(a): finite qubit Werner sharing thresholds
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   For each $1\le m,n\le5$ and each qubit Werner parameter $\psi\in[-1,1]$,
--   $$\rho_W(\psi)\text{ is }m\text{-}n\text{ sharable}\quad\Longleftrightarrow\quad\psi\ge-\frac1{\max(m,n)}.$$
--   This compact formula records exactly all 25 entries of Table I(a), with the table's quantity interpreted as $-\psi$.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 12, Table I(a): finite qubit Werner sharing thresholds

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Table I(a), PDF p.12: all 25 printed finite qubit sharing thresholds. -/
theorem table_qubit_thresholds (m n : ℕ) (hm : 1 ≤ m ∧ m ≤ 5) (hn : 1 ≤ n ∧ n ≤ 5)
    (psi : ℝ) (hpsi : -1 ≤ psi ∧ psi ≤ 1) :
    Sharable m n (wernerSwapState 2 psi) ↔ -(1/(max m n : ℝ)) ≤ psi := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
