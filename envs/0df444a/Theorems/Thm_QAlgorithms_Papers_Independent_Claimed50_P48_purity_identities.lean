-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_purity_identities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.purity_identities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:38:56.875327+00:00
-- url     : https://prove2.me/theorems/15221555-e133-48c7-9315-806655e87f0c
-- title:
--   Equations (7)–(9): invariance of output-purity characteristics
-- statement:
--   Let $\Phi,\widetilde\Phi$ be complementary CP maps on a common nonzero finite input space. For every real Schatten exponent $p\ge1$ and the operator-norm endpoint $p=\infty$,
--
--   $$\nu_p(\widetilde\Phi)=\nu_p(\Phi).$$
--
--   If $\Phi$ is a channel, its complement is a channel and
--
--   $$\check H(\widetilde\Phi)=\check H(\Phi),\qquad
--   \widehat H_{\widetilde\Phi}(\rho)=\widehat H_\Phi(\rho)\quad\text{for every input density }\rho.$$
--
--   Entropies use natural logarithms, and the convex roof optimizes all finite normalized pure decompositions of the specified density. The last identity is an equality of functions on the state space.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 3, Equations (7)–(9): invariance of output-purity characteristics

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

/-- Equations (7)–(9), PDF p.3, using p.2 definitions. (9) is equality
on EVERY density in the common input space. -/
theorem purity_identities [Nonempty A] (Phi : Superop A B) (Psi : Superop A C)
    (h : CPComplementary Phi Psi) (p : ℝ≥0∞) (hp : ValidExponent p) :
    nu p Psi = nu p Phi ∧ (IsChannel Phi → IsChannel Psi ∧ hmin Psi = hmin Phi ∧
      ∀ rho, IsDensityMatrix rho → hhat Psi rho = hhat Phi rho) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
