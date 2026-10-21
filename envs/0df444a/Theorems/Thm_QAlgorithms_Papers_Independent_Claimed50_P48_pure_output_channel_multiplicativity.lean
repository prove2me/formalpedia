-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_pure_output_channel_multiplicativity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.pure_output_channel_multiplicativity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:51:33.827458+00:00
-- url     : https://prove2.me/theorems/75de112f-3a45-4e32-86a2-093cfcc30f27
-- title:
--   A channel with nu_p=1 is multiplicative with every CP partner
-- statement:
--   Let $\Phi$ be a channel on a nonzero finite input space and let $1\le p\le\infty$. If $\nu_p(\Phi)=1$, then for every finite-dimensional CP map $\Psi$ with nonzero input,
--
--   $$\nu_p(\Phi\otimes\Psi)=\nu_p(\Phi)\nu_p(\Psi).$$
--
--   The partner need not preserve trace, and the tensor product is optimized over all joint densities. This is the general assertion proved in the paragraph, with diagonal channels as examples.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 6, A channel with nu_p=1 is multiplicative with every CP partner

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

/-- PDF p.6: channel with nu_p=1, EVERY CP partner, all joint inputs. -/
theorem pure_output_channel_multiplicativity [Nonempty A]
    (Phi : Superop A B) (hPhi : IsChannel Phi)
    (p : ℝ≥0∞) (hp : ValidExponent p) (hnu : nu p Phi = 1) :
    UniversalMultiplicative p Phi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
