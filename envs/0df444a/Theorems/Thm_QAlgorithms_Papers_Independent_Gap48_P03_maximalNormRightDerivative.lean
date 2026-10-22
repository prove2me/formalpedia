-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_maximalNormRightDerivative
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.maximalNormRightDerivative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:54:55.3244+00:00
-- url     : https://prove2.me/theorems/9fe4bc78-5405-4a65-8d62-aa18037b4558
-- title:
--   Right derivative of maximal output norm at one
-- statement:
--   Let $\Psi$ be any completely positive trace-preserving map between arbitrary nonzero finite-dimensional complex matrix spaces; its input and output dimensions may differ. Here $S_{\min}$ is the infimum of output von Neumann entropy over all input states, $\nu_p$ is the supremum of the positive Schatten $p$-norm over those states, and $\chi^*$ is the supremum of the output Holevo information over all finite normalized input ensembles. The maximal output norm has a right derivative at $p=1$, with
--
--   $$\left.\frac{d}{dp^+}\nu_p(\Psi)\right|_{p=1}=-S_{\min}(\Psi).$$
--
--   The entropy is in nats. This identity relates the source’s two channel noisiness functionals at their shared endpoint.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 3, Unnumbered identity (7): entropy as the right derivative of maximal output p-norm

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

namespace QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0204172v2, PDF p.3, (7): right derivative at p=1, in natural units. -/
theorem maximalNormRightDerivative {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (Psi : Superop A B) (hPsi : IsChannel Psi) :
    HasDerivWithinAt (maximumOutputPNorm Psi) (-(minimumOutputEntropy Psi).toReal) (Set.Ici 1) 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
