-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_ebt_amplification_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.ebt_amplification_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:39:34.201479+00:00
-- url     : https://prove2.me/theorems/bed4a240-3fab-41cc-b00f-37d23a70adb3
-- title:
--   Lemma 15: EBT amplification bound
-- statement:
--   Let $\Phi:M_m\to M_n$ be an entanglement-breaking trace-preserving channel, where $m,n\ge1$. For every exponent $1\le p\le\infty$ and every positive semidefinite $Q\in M_n\otimes M_m$, one has
--
--   $$\|(\mathrm{id}_n\otimes\Phi)(Q)\|_p\le\|\operatorname{Tr}_2 Q\|_p.$$
--
--   The ancillary dimension is precisely the displayed output dimension $n$, and $Q$ need not be normalized. Entanglement breaking means that every finite-reference density input has separable output. This bounds the output norm in terms of the unaffected marginal.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 25, Lemma 15: EBT amplification bound

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

/-- Lemma 15 / (5.9), PDF p.25: the prescribed ancilla is the output dimension.
The input Q is arbitrary PSD and need not have trace one. -/
theorem ebt_amplification_bound {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Phi : (Mat I →ₗ[ℂ] Mat J)) (hPhi : IsEBT Phi) (Q : Mat (J × I)) (hQ : Q.PosSemidef) :
    schattenNorm p (idTensorSuperop Phi Q) ≤ schattenNorm p (traceRight Q) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
