-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P39_single_letter_iff_tensor_additivity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P39.single_letter_iff_tensor_additivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:50:50.374451+00:00
-- url     : https://prove2.me/theorems/34ce82f9-ca90-4d62-890d-20787362160a
-- title:
--   Single-letter ordinary capacity iff tensor-power Holevo additivity
-- statement:
--   Let $\mathcal N:A\to B$ be any quantum channel between positive, finite-dimensional complex Hilbert spaces. Let $C(\mathcal N)$ be its ordinary unassisted classical capacity, defined operationally by vanishing uniform-message average decoding error and asymptotic communication rate, allowing arbitrary input entanglement across forward uses. Let $\chi(\mathcal N)$ be the supremum of the output Holevo information over all finite ensembles of mixed input density operators. Entropies and rates are in bits. Then
--
--   $$
--   C(\mathcal N)=\chi(\mathcal N)
--   \quad\Longleftrightarrow\quad
--   \forall n\ge1,\quad \chi(\mathcal N^{\otimes n})=n\chi(\mathcal N).
--   $$
--
--   The tensor channel is the actual product map on all operators, including entangled inputs. No entanglement-breaking assumption is imposed. This equivalence characterizes when the operational capacity has a single-use Holevo formula.
-- source:
--   Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels, arXiv:1506.02228v4, PDF p. 15, Appendix A; (1.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P39

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD tensorAction)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Support50.P19
  (channelInformation informationRadius expTwo)

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- PDF pp.2,15, (1.5) and Appendix A: ordinary unassisted capacity is single-letter
iff all positive tensor powers have additive Holevo information; N need not be EB. -/
theorem single_letter_iff_tensor_additivity [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) :
    ordinaryClassicalCapacity N = channelHolevo N ↔
      ∀ n : ℕ, 0 < n → channelHolevo (channelPower N n) =
        (n : ℝ) * channelHolevo N := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P39

end
