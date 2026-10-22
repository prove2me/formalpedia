-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P09_proposition6
-- name    : QAlgorithms.Papers.Independent.Gap20.P09.proposition6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:24:36.835876+00:00
-- url     : https://prove2.me/theorems/d567b999-3d55-4848-b45a-974f388902a3
-- title:
--   Proposition 6: CEMI bounds multipartite squashed entanglement
-- statement:
--   All registers below have finite, strictly positive dimension. States are positive semidefinite operators of trace one, channels are completely positive and trace preserving, and marginals are partial traces of the same state. Entropies use natural logarithms, with $0\log0=0$, and $\|\cdot\|_1$ denotes the full Schatten trace norm.
--
--   Let $\rho$ be a state on $A_1\cdots A_l$, $l\ge1$. Define
--   $$E_{\rm sq}(\rho)=\frac12\inf_{\omega_{A_1\cdots A_lE}:\operatorname{Tr}_E\omega=\rho}\left[\sum_{i=1}^l H(A_i\mid E)_\omega-H(A_1\cdots A_l\mid E)_\omega\right],$$
--   where $H(X\mid E)=H(XE)-H(E)$ and the infimum allows every positive finite dimension for $E$. Also set
--   $$E_I(\rho)=\frac12\inf_{\sigma:\operatorname{Tr}_{A'_1\cdots A'_l}\sigma=\rho}\left[I(A_1A'_1:\cdots:A_lA'_l)_\sigma-I(A'_1:\cdots:A'_l)_\sigma\right],$$
--   where all positive finite local ancillary dimensions are allowed. Then
--   $$E_{\rm sq}(\rho)\le E_I(\rho).$$
--
--   This compares two unrestricted-extension entanglement measures; both use the same factor one half and natural-log units.
-- source:
--   Multipartite quantum correlations and local recoverability, arXiv:1412.0333v3, PDF p. 12, Proposition 6: CEMI bounds multipartite squashed entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

-- Exact accepted heterogeneous and selected-register bases; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Gap48.P22
  (ReplicaBasis partyCopyMultiplicity selectedReplicaMarginal)

/-- PDF p.12, Proposition 6,(5.25): both measures include the factor one half. -/
theorem proposition6 {l : ℕ} (hl : 0 < l) {D : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    multipartiteSquashedNats rho ≤ cemi rho := by sorry

end QAlgorithms.Papers.Independent.Gap20.P09

end
