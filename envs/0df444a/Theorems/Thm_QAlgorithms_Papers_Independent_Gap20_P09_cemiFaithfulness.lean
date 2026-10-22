-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P09_cemiFaithfulness
-- name    : QAlgorithms.Papers.Independent.Gap20.P09.cemiFaithfulness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:23:28.025395+00:00
-- url     : https://prove2.me/theorems/42ec7a17-2413-4a19-941f-49abbfb93872
-- title:
--   §5, unnumbered: CEMI vanishes exactly on fully separable states
-- statement:
--   All registers below have finite, strictly positive dimension. States are positive semidefinite operators of trace one, channels are completely positive and trace preserving, and marginals are partial traces of the same state. Entropies use natural logarithms, with $0\log0=0$, and $\|\cdot\|_1$ denotes the full Schatten trace norm.
--
--   Let $\rho$ be a state on $A_1\cdots A_l$, $l\ge1$. Its conditional entanglement of multipartite information is
--   $$E_I(\rho)=\frac12\inf_{\omega:\operatorname{Tr}_{A'_1\cdots A'_l}\omega=\rho}\left[I(A_1A'_1:\cdots:A_lA'_l)_\omega-I(A'_1:\cdots:A'_l)_\omega\right],$$
--   where all finite positive ancillary dimensions and all normalized extensions are allowed. Then
--   $$E_I(\rho)=0\quad\Longleftrightarrow\quad\rho\text{ is fully separable}.$$
--   Fully separable means that $\rho=\sum_z p_z\,\sigma_1^z\otimes\cdots\otimes\sigma_l^z$ for a finite probability distribution $(p_z)$ and normalized local states $\sigma_i^z$.
--
--   This gives qualitative faithfulness of ordinary CEMI independently of the disputed numerical prefactor in Proposition 4.
-- source:
--   Multipartite quantum correlations and local recoverability, arXiv:1412.0333v3, PDF p. 9, §5, unnumbered: CEMI vanishes exactly on fully separable states

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

/-- PDF p.9, Section 5: ordinary CEMI vanishes exactly on FULLY separable states.
No disputed numerical coefficient from Proposition 4 enters this statement. -/
theorem cemiFaithfulness {l : ℕ} (hl : 0 < l)
    (s : QAlgorithms.Papers.Independent.Claimed50.P33.FiniteState l) :
    cemi s.rho = 0 ↔
      QAlgorithms.Papers.Independent.Claimed50.P33.IsMixedFullySeparable s := by sorry

end QAlgorithms.Papers.Independent.Gap20.P09

end
