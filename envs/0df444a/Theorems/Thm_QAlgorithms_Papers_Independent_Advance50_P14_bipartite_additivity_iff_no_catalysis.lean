-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_bipartite_additivity_iff_no_catalysis
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.bipartite_additivity_iff_no_catalysis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:24:23.691683+00:00
-- url     : https://prove2.me/theorems/0a0ed345-2c89-43cd-a100-118b4429c6d3
-- title:
--   Lemma VI.3, equation (30): bipartite additivity iff no catalysis
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. Restrict to bipartite states, with arbitrary positive finite local dimensions. Full additivity is the property
--
--   $$\forall\rho,\pi,\quad E_R^\infty(\rho\otimes\pi)=E_R^\infty(\rho)+E_R^\infty(\pi).$$
--
--   This property holds if and only if there is no catalyst anywhere in the bipartite asymptotically non-entangling conversion theory: for all states and catalysts, conversion with the same returned catalyst implies conversion without it. The equivalence asserts neither side unconditionally and does not extend the no-catalysis conclusion to multipartite systems.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 20, Lemma VI.3, equation (30): bipartite additivity iff no catalysis

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.20, Lemma VI.3, Eq.(30): full additivity for ALL bipartite states
iff absence of catalysis throughout the BIPARTITE theory. The next paragraph
leaves a multipartite extension open, so none is asserted here. -/
theorem bipartite_additivity_iff_no_catalysis :
    (∀ A B : MultipartiteRegister 2, ∀ (rho : PartyOperator A) (pi : PartyOperator B),
      IsDensityMatrix rho → IsDensityMatrix pi →
      regularizedMultipartiteEntanglement (tensorRegister A B) (partyTensorDensity A B rho pi) =
        regularizedMultipartiteEntanglement A rho + regularizedMultipartiteEntanglement B pi) ↔
      NoCatalysisAt 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
