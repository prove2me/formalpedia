-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_table_dimension_four_thresholds
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.table_dimension_four_thresholds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:08:45.629949+00:00
-- url     : https://prove2.me/theorems/1630d93b-da18-4411-8dd9-6ad92dba1a16
-- title:
--   Table I(c): computed d=4 Werner sharing thresholds
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   In dimension $d=4$, Table I(c) supplies the following symmetric thresholds $t_{mn}$, with rows and columns labeled $1,\ldots,5$:
--   $$\begin{pmatrix}1&1&1&3/4&3/5\\1&1&2/3&1/2&1/2\\1&2/3&5/9&1/2&*\\3/4&1/2&1/2&*&*\\3/5&1/2&*&*&*\end{pmatrix}.$$
--   For each specified entry and $\psi\in[-1,1]$,
--   $$\rho_W(\psi)\text{ is }m\text{-}n\text{ sharable}\quad\Longleftrightarrow\quad\psi\ge-t_{mn}.$$
--   Asterisks are uncomputed entries and impose no assertion.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 12, Table I(c): computed d=4 Werner sharing thresholds

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Table I(c), PDF p.12: exactly the computed d=4 entries, including (3,3)=5/9.
The option-valued table excludes every uncomputed entry from this statement. -/
theorem table_dimension_four_thresholds (m n : ℕ) (t : ℝ) (hentry : tableFour m n = some t)
    (psi : ℝ) (hpsi : -1 ≤ psi ∧ psi ≤ 1) :
    Sharable m n (wernerSwapState 4 psi) ↔ -t ≤ psi := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
