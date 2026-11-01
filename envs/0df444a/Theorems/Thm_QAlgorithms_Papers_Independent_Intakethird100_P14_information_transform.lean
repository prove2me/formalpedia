-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_information_transform
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.information_transform
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:58:12.024011+00:00
-- url     : https://prove2.me/theorems/0034274e-fa6b-455d-a918-2de330479e49
-- title:
--   Conservation and ordering of symmetric information
-- statement:
--   Let $W:b\mapsto\rho_b$ be a binary-input classical–quantum channel with normalized density outputs. Construct the channels $W^-$ and $W^+$ exactly by (14)–(15): apply the binary polar kernel to two independent uniform bits, average the second bit for $W^-$, and retain the first bit as a classical register for $W^+$. Their uniform-prior Holevo informations, measured in bits, satisfy
--
--   $$I(W^-)+I(W^+)=2I(W),\qquad I(W^-)\le I(W^+),\qquad I(W^-)\le I(W)\le I(W^+).$$
--
--   This includes both numbered assertions and the immediately displayed consequence. The channels are constructed from $W$; conservation is not a premise on arbitrary supplied channels. These identities describe movement of information away from the center while preserving total rate.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 7, Proposition 8: conservation and ordering of symmetric Holevo information

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P14

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (compression)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 8 and its displayed consequence, PDF p.7; proof pp.10–11.
The minus/plus channels are computed from W, not supplied with conservation
as a hypothesis. Uniform independent bits are in (14)–(15). -/
theorem information_transform {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W) :
    symmetricInformation (channelMinus W) + symmetricInformation (channelPlus W) =
      2 * symmetricInformation W ∧
    symmetricInformation (channelMinus W) ≤ symmetricInformation (channelPlus W) ∧
    symmetricInformation (channelMinus W) ≤ symmetricInformation W ∧
    symmetricInformation W ≤ symmetricInformation (channelPlus W) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
