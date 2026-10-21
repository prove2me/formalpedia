-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_eb_cp_multiplicativity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.eb_cp_multiplicativity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:47:27.174291+00:00
-- url     : https://prove2.me/theorems/20991aa9-4a7f-4c7c-acc1-7bfe589a432a
-- title:
--   Extension of King multiplicativity to entanglement-breaking CP maps
-- statement:
--   Let $\Phi$ be a finite-dimensional entanglement-breaking CP map in the rank-one Kraus sense, with nonzero input space. For every finite real $p>1$ and every finite-dimensional CP partner $\Psi$ with nonzero input,
--
--   $$\nu_p(\Phi\otimes\Psi)=\nu_p(\Phi)\nu_p(\Psi).$$
--
--   Neither map is required to preserve trace. This is the paper's explicit extension of the cited channel multiplicativity result; endpoint extensions are not included in this statement.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 5, Extension of King multiplicativity to entanglement-breaking CP maps

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- PDF p.5: this paper extends King multiplicativity to EB CP maps.
Finite p>1 is the printed range; endpoint extensions are not bundled in. -/
theorem eb_cp_multiplicativity [Nonempty A] (Phi : Superop A B) (hPhi : HasRankOneKraus Phi) :
    ∀ p : ℝ, 1 < p → UniversalMultiplicative (ENNReal.ofReal p) Phi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
