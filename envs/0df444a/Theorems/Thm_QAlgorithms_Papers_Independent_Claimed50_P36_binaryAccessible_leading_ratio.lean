-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P36_binaryAccessible_leading_ratio
-- name    : QAlgorithms.Papers.Independent.Claimed50.P36.binaryAccessible_leading_ratio
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:36:43.035805+00:00
-- url     : https://prove2.me/theorems/55af6e31-46d0-4c15-b6c3-88a9208f9497
-- title:
--   Binary accessible information realizes the leading weak-energy rate
-- statement:
--   Let $C_1^{(2)}(m)$ be the supremum of the one-symbol Shannon mutual information over all binary coherent alphabets, all priors $Q\in[0,1]$, and optimized receiver POVMs, subject to $Q|\alpha|^2+(1-Q)|\beta|^2\le m$. Let $C_{\rm BE}(m)$ denote the noiseless continuous coherent capacity with collective decoding, in the same natural-log units. Then
--
--   $$
--   \lim_{m\downarrow0}\frac{C_1^{(2)}(m)}{C_{\rm BE}(m)}=1.
--   $$
--
--   The one-symbol optimization is bounded for nonnegative budgets. It is the full supremum, not the value of the approximate prior in (79). The result asserts the leading-rate equivalence only, with no convergence speed or second-order accessible-information expansion.
-- source:
--   Information capacity formula of quantum optical channels, arXiv:quant-ph/0105042v1, PDF p. 18, Convergence sentence following Eq.(80)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P36

open Filter

open scoped Topology ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable

-- Reuse the pinned accepted entropy definitions, preserving their codomains
-- and units. P24.bosonicEntropy is in bits: multiply by log 2 for nats.
-- P01.binaryEntropy is in nats and ENNReal-valued: use toReal only at the
-- finite binary-probability argument of binaryValue below.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

/-- PDF p.18, convergence sentence after (80): the full single-symbol binary
accessible-information optimization realizes the leading coherent capacity.
No convergence speed, heuristic optimizer, or second-order term is asserted. -/
theorem binaryAccessible_leading_ratio :
    (∀ m : ℝ, 0 ≤ m → BddAbove (binaryAccessibleValues m)) ∧
    Tendsto (fun m : ℝ => binaryAccessibleCapacity m / coherentCapacity m)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P36

end
