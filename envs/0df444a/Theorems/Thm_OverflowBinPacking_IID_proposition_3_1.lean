-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_proposition_3_1
-- name    : OverflowBinPacking.IID.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:32.270483+00:00
-- url     : https://prove2.me/theorems/ddf2a248-97dd-4eaf-b922-f71f2e66199a
-- title:
--   Proposition 3.1, pp. 8–9 — expected number of broken bins equals accumulated risk
-- statement:
--   Let independent nonnegative item sizes be packed by a deterministic feasible policy $P$. If $S_j^{i-1}$ is bin $j$'s load before item $i$, and $1^P_{i\to j}$ indicates its assignment to that bin, then
--   $$\mathbb E[O_P]=\sum_{j=1}^{n}\mathbb E\!\left[\sum_{i=1}^{n}\Pr(X_i+S_j^{i-1}>1)1^P_{i\to j}\right].$$
--   More precisely, for each bin $j$, its breaking probability equals the expected sum of its placement risks. Summing those identities gives the displayed formula. This links the physical overflow count to the risk budget used later.
--
--   **Formalization Note** The per-bin identity comes from the proof on p. 33. The policy is measurable and feasible; $C\ge1$ is the standing cost convention, although the identity does not depend on its value.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, pp. 8–9, Proposition 3.1; p. 33, proof

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Model

namespace OverflowBinPacking.IID

open MeasureTheory

/-- Proposition 3.1, pp. 8–9, including the per-bin identity proved on p. 33. -/
theorem proposition_3_1 {n : ℕ} (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C : ℝ) (hC : 1 ≤ C) (a : Rule n) (ha : IsPolicy a) :
    (∀ j : Fin n,
      (Measure.pi μ).real {x | 1 < usage a x j n} =
        ∫ x, risk μ a x j ∂(Measure.pi μ)) ∧
    (∫ x, (numBroken a x : ℝ) ∂(Measure.pi μ)) =
      ∫ x, (∑ j : Fin n, risk μ a x j) ∂(Measure.pi μ) := by sorry

end OverflowBinPacking.IID
