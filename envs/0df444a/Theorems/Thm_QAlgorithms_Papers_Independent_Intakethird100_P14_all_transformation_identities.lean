-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_all_transformation_identities
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.all_transformation_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:59:22.277138+00:00
-- url     : https://prove2.me/theorems/cbe432bf-c1c8-470a-abaf-f9cee0dca462
-- title:
--   All local and cumulative information and fidelity identities
-- statement:
--   Let $W$ be a binary-input classical–quantum channel with normalized density outputs. For $N=2^n$, $n\ge0$, write $I_i=I(W_N^{(i)})$ and $f_i=\sqrt{F(W_N^{(i)})}$, where information uses the uniform prior and bits, and $F$ is squared fidelity. Write $I_{i,-},f_{i,-}$ and $I_{i,+},f_{i,+}$ for the corresponding quantities of children $W_{2N}^{(2i-1)}$ and $W_{2N}^{(2i)}$. For every $1\le i\le N$,
--
--   $$I_{i,-}+I_{i,+}=2I_i,\qquad f_{i,-}+f_{i,+}\le2f_i,$$
--   $$I_{i,-}\le I_i\le I_{i,+},\qquad f_{i,-}\ge f_i\ge f_{i,+},$$
--   $$f_{i,+}=F(W_N^{(i)}),\qquad f_{i,-}\le2f_i-F(W_N^{(i)}).$$
--
--   The cumulative quantities also satisfy
--
--   $$\sum_{i=1}^N I_i=NI(W),\qquad \sum_{i=1}^N f_i\le N\sqrt{F(W)}.$$
--
--   This states the entire proposition through (29), including both unnumbered ordering displays. It propagates the single-step transform to every level of the actual channel tree.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 8, Proposition 10: all local and cumulative transformation identities (24)–(29)

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

/-- Proposition 10, PDF p.8: every local assertion (24)–(27), both
unnumbered ordering displays, and cumulative (28)–(29). -/
theorem all_transformation_identities {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W)
    (n : ℕ) :
    (∀ i : PolarWire n,
      symmetricInformation (splitChannel W (n + 1) (childIndex i false)) +
        symmetricInformation (splitChannel W (n + 1) (childIndex i true)) =
          2 * symmetricInformation (splitChannel W n i) ∧
      Real.sqrt (squaredCqFidelity (splitChannel W (n + 1) (childIndex i false))) +
        Real.sqrt (squaredCqFidelity (splitChannel W (n + 1) (childIndex i true))) ≤
          2 * Real.sqrt (squaredCqFidelity (splitChannel W n i)) ∧
      symmetricInformation (splitChannel W (n + 1) (childIndex i false)) ≤
        symmetricInformation (splitChannel W n i) ∧
      symmetricInformation (splitChannel W n i) ≤
        symmetricInformation (splitChannel W (n + 1) (childIndex i true)) ∧
      Real.sqrt (squaredCqFidelity (splitChannel W n i)) ≤
        Real.sqrt (squaredCqFidelity (splitChannel W (n + 1) (childIndex i false))) ∧
      Real.sqrt (squaredCqFidelity (splitChannel W (n + 1) (childIndex i true))) ≤
        Real.sqrt (squaredCqFidelity (splitChannel W n i)) ∧
      Real.sqrt (squaredCqFidelity (splitChannel W (n + 1) (childIndex i true))) =
        squaredCqFidelity (splitChannel W n i) ∧
      Real.sqrt (squaredCqFidelity (splitChannel W (n + 1) (childIndex i false))) ≤
        2 * Real.sqrt (squaredCqFidelity (splitChannel W n i)) - squaredCqFidelity (splitChannel W n i)) ∧
    (∑ i : PolarWire n, symmetricInformation (splitChannel W n i)) =
      (2 ^ n : ℕ) * symmetricInformation W ∧
    (∑ i : PolarWire n, Real.sqrt (squaredCqFidelity (splitChannel W n i))) ≤
      (2 ^ n : ℕ) * Real.sqrt (squaredCqFidelity W) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
