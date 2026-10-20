-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_causalHistories_feasible
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.causalHistories_feasible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:48:54.341723+00:00
-- url     : https://prove2.me/theorems/6dab7022-43b7-4b43-8230-f664a7278419
-- title:
--   §VI question 3: causality implies feasible multi-time measurement
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $N,k\ge1$ and let Kraus histories $R_i=\sum_a|K_{ia}\rangle\rangle\langle\langle K_{ia}|$ have a total satisfying every recursive causality normalization. Then they have one physical realization by $N$ isometric interactions with quantum memories and a final von Neumann measurement of a $k$-dimensional ancilla:
--
--   $$
--   R_i=C(\text{physical branch }i)\quad\text{for every }i.
--   $$
--
--   Other memory dimensions are unrestricted. The claim applies to the ordered comb model of the paper, not independent-teeth domains or general probabilistic theories.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 21, §VI question 3: causality implies feasible multi-time measurement

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.21, question 3 and Fig.12: causal Kraus histories have a common feasible
isometric scheme followed by measurement of a k-dimensional factor. -/
theorem causalHistories_feasible (s : Signature) (n k q : ℕ)
    (hn : 0 < n) (hk : 0 < k) (K : Fin k → Fin q → Basis s n → ℂ)
    (hcausal : Normalized s n (∑ i, ∑ a, rankOne (K i a))) :
    MeasuredRealization s n k (fun i => ∑ a, rankOne (K i a)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
