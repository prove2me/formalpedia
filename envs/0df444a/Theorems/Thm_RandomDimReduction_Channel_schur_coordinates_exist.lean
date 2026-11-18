-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_schur_coordinates_exist
-- name    : RandomDimReduction.Channel.schur_coordinates_exist
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T19:50:50.787926+00:00
-- url     : https://prove2.me/theorems/a2a08461-6ed9-438b-8106-834c1816747f
-- title:
--   Compatible labelled Schur coordinates exist in every positive dimension
-- statement:
--   Let $n$ be a positive integer. There is a unitary model $\kappa_\lambda$ of each labelled Specht representation, chosen once for this $n$, such that for every positive integer $d$ there is a unitary Schur coordinate transformation $S_{d,n}$ satisfying
--   $$S_{d,n}P_\pi A^{\otimes n}S_{d,n}^\dagger=\bigoplus_{\lambda\vdash n}\kappa_\lambda(\pi)\otimes\nu_\lambda^d(A)$$
--   for every permutation $\pi\in S_n$ and every complex $d\times d$ matrix $A$, including singular matrices. The multiplicity factors have the dimensions of the published Schur modules; shapes with more than $d$ rows have zero-dimensional multiplicity factors. The labels are fixed by unitary equivalence to the published Young-ideal Specht construction.
--
--   This is the algebraic existence assertion of the Schur–Weyl decomposition in Eq. (13). Sharing the Specht model across ambient dimensions makes rectangular isometry comparisons possible. No circuit-size or approximation assertion is included.
-- source:
--   Angus Lowe and Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Section 5.1, p.15, Schur–Weyl decomposition and Eq.(13), with the polynomial extension to every complex matrix specified immediately before Eq.(13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf . Algebraic background also stated in Burchardt et al., High-dimensional quantum Schur transforms, arXiv:2509.22640v1, Section2.1 Eqs.(1)–(2).

import Definitions.Def_RandomDimReduction_Channel_Schur

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem schur_coordinates_exist (n : ℕ) (hn : 0 < n) :
    ∃ κ : SpechtModel n, ∀ d : ℕ, 1 ≤ d → Nonempty (SchurTransform κ d) := by sorry

end RandomDimReduction.Channel
