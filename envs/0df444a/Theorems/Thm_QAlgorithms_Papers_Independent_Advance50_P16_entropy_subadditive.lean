-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_entropy_subadditive
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.entropy_subadditive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:49:27.446709+00:00
-- url     : https://prove2.me/theorems/6b84929d-1ed7-4d3b-a6cc-a2b32bf01a20
-- title:
--   §6, (6.1): subadditivity via mixed-norm differentiation
-- statement:
--   Let $Q$ be any density matrix on a nonzero finite bipartite register, and let $Q_1=\operatorname{Tr}_2Q$ and $Q_2=\operatorname{Tr}_1Q$. Then its von Neumann entropy in nats satisfies
--
--   $$S(Q)\le S(Q_1)+S(Q_2).$$
--
--   No purity, full rank, or additional inequality is assumed. This is the unnumbered subadditivity conclusion recovered in (6.1).
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 28, §6, (6.1): subadditivity via mixed-norm differentiation

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- (6.1), PDF p.28: subadditivity for arbitrary mixed densities.
The erroneous intervening mixed-norm identity is not used as an assumption. -/
theorem entropy_subadditive {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (Q : Mat (A × B)) (hQ : IsDensityMatrix Q) :
    entropy Q ≤ entropy (traceRight Q) + entropy (traceLeft Q) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
