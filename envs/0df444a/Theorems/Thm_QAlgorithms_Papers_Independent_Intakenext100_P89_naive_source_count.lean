-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P89_naive_source_count
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P89.naive_source_count
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:27:42.043065+00:00
-- url     : https://prove2.me/theorems/5bd4e218-2e72-436c-b176-2500683a44e1
-- title:
--   Naive multiplexing: simultaneous source count
-- statement:
--   Let $k\in\mathbb N$ be the fusion depth and let $n_{\rm GHZ},n_B,n_{\rm meas}$ be positive integers. In the unboosted naive stack, each leaf GHZ state is selected from $n_{\rm GHZ}$ independent attempts, each using six single-photon sources; each fusion has $n_B$ attempts, each needing two daughter stacks. There are $n_{\rm meas}$ complete top-level copies. The number of simultaneously fired sources is
--
--   $$N_s=6n_{\rm GHZ}n_{\rm meas}(2n_B)^k.$$
--
--   The formal source set labels each of these sources explicitly. This count is for the specified baseline and does not include the ancillary photons of the improved boosted protocol.
-- source:
--   Rate-distance tradeoff and resource costs for all-optical quantum repeaters, arXiv:1603.01353v4, PDF p. 7, III.A.1: naive multiplexing source count

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

namespace QAlgorithms.Papers.Independent.Intakenext100.P89

open scoped BigOperators ComplexConjugate

-- Accepted probability primitives: symbol true is success; choose n x is zero for x > n.

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)

open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

noncomputable section

/-- Source p.7, III.A.1: simultaneous sources in the unboosted naive multiplexing stack.
Additional boosted-fusion ancillas are not included in this count. -/
theorem naive_source_count (k nGHZ nB nMeas : ℕ)
    (hGHZ : 0 < nGHZ) (hB : 0 < nB) (hMeas : 0 < nMeas) :
    Fintype.card (NaiveSources k nGHZ nB nMeas) =
      6 * nGHZ * nMeas * (2 * nB) ^ k := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P89
