-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_twirled_extensions_preserve_marginals
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.twirled_extensions_preserve_marginals
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:05:29.901045+00:00
-- url     : https://prove2.me/theorems/aa93e790-5c5a-483e-b047-4bed16edd4cd
-- title:
--   Sec. III C, unnumbered: twirling preserves the required marginals
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.
--
--   Let $w$ be a tripartite density operator. If its AB and AC marginals are Werner states, their values are preserved by the normalized Haar twirl with $U\otimes U\otimes U$. If they are isotropic states, their values are preserved by the twirl with $\overline U\otimes U\otimes U$. In either case, with the appropriate $G_U$,
--   $$\widetilde w=\int G_UwG_U^\dagger d\mu(U)\quad\text{is a density operator with the same prescribed AB and AC marginals}.$$
--   These are the two invariant search-space reductions used in Sec.III C.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 8, Sec. III C, unnumbered: twirling preserves the required marginals

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Eqs.(13),(18), PDF p.8: both twirls preserve the required AB and AC marginals. -/
theorem twirled_extensions_preserve_marginals (d : ℕ) (hd : 2 ≤ d) :
    (∀ (a b : ℝ) (X : Op (Fin d × Fin d × Fin d)),
      JoinsTwo X (wernerSwapState d a) (wernerSwapState d b) →
      JoinsTwo (tripleTwirl false X) (wernerSwapState d a) (wernerSwapState d b)) ∧
    (∀ (a b : ℝ) (X : Op (Fin d × Fin d × Fin d)),
      JoinsTwo X (isotropicOverlapState d a) (isotropicOverlapState d b) →
      JoinsTwo (tripleTwirl true X) (isotropicOverlapState d a) (isotropicOverlapState d b)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
