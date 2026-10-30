-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_oneShot_comparison
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.oneShot_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:34:59.058991+00:00
-- url     : https://prove2.me/theorems/058cec3f-851b-47c3-82d0-c894bd03f6cd
-- title:
--   Comparison of the two one-shot capacities
-- statement:
--   Let $\Phi:\mathcal B(A)\to\mathcal B(B)$ be a CPTP map between nonzero finite-dimensional registers, and let $\epsilon>0$. The capacities $Q_{\rm ent}$ and $Q_{\min}$ optimize $\log_2m$ over subspaces of positive integer rank $m\le\dim A$ and arbitrary CPTP decoders, using respectively maximally entangled overlap and worst-case unit-vector overlap with required accuracy at least $1-\epsilon$. Then
--
--   $$Q_{\rm ent}(\Phi;\epsilon)-1\le Q_{\min}(\Phi;2\epsilon)\le Q_{\rm ent}(\Phi;4\epsilon).$$
--
--   All three operational maxima have feasible code witnesses. The error rescalings quantify the comparison between the two transmission criteria.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 5, Corollary 1, comparison of one-shot capacities

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

/-- Corollary 1, PDF p.5: both error rescalings and the one-bit loss.
Operational maxima are witnessed in the conclusion. -/
theorem oneShot_comparison {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) (eps : ℝ) (heps : 0 < eps) :
    qEnt Phi eps - 1 ≤ qMin Phi (2*eps) ∧ qMin Phi (2*eps) ≤ qEnt Phi (4*eps) ∧
    EntRate Phi eps (qEnt Phi eps) ∧ MinRate Phi (2*eps) (qMin Phi (2*eps)) ∧
    EntRate Phi (4*eps) (qEnt Phi (4*eps)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
