-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_fidelity_transform
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.fidelity_transform
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:58:47.220836+00:00
-- url     : https://prove2.me/theorems/f195d523-b723-46ee-9cad-03b7cfeb9d16
-- title:
--   Fidelity transform and improvement of total root reliability
-- statement:
--   Let $W$ be any binary-input classical–quantum channel with normalized density outputs, and let $W^-$ and $W^+$ be the actual transforms (14)–(15), including the uniform classical flag for $W^+$. For squared fidelity $F$, all of the following hold:
--
--   $$\sqrt{F(W^+)}=F(W),\qquad
--   \sqrt{F(W^-)}\le2\sqrt{F(W)}-F(W),\qquad
--   F(W^-)\ge F(W)\ge F(W^+),$$
--   $$\sqrt{F(W^-)}+\sqrt{F(W^+)}\le2\sqrt{F(W)}.$$
--
--   The last display is the immediate consequence on page 8. The endpoints $F(W)=0$ and $F(W)=1$ are included. The final prose on page 12 reverses the last ordering; the formalization retains numbered (23), consistent with $F(W^+)=F(W)^2$. These relations control reliability throughout the polarization tree.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 7, Proposition 9: fidelity transformation

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

/-- Proposition 9, (21)–(23), PDF p.7, and consequence p.8; proof pp.11–12.
The last prose inequality on p.12 is reversed; we retain numbered (23), as
also fixed by F(W+)=F(W)^2. Endpoints F=0 and F=1 are included. -/
theorem fidelity_transform {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W) :
    Real.sqrt (squaredCqFidelity (channelPlus W)) = squaredCqFidelity W ∧
    Real.sqrt (squaredCqFidelity (channelMinus W)) ≤
      2 * Real.sqrt (squaredCqFidelity W) - squaredCqFidelity W ∧
    squaredCqFidelity W ≤ squaredCqFidelity (channelMinus W) ∧
    squaredCqFidelity (channelPlus W) ≤ squaredCqFidelity W ∧
    Real.sqrt (squaredCqFidelity (channelMinus W)) + Real.sqrt (squaredCqFidelity (channelPlus W)) ≤
      2 * Real.sqrt (squaredCqFidelity W) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
