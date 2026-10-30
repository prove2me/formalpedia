-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_nonnegative_entropy_not_ebt
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.nonnegative_entropy_not_ebt
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:48:37.342582+00:00
-- url     : https://prove2.me/theorems/2020135f-c08f-41a5-a0ea-8732d30defdb
-- title:
--   §5.2: nonnegative CB entropy does not characterize EBT
-- statement:
--   For every integer $d>3$, let $\Phi_{\mathrm{WH}}$ be the Werner–Holevo channel $X\mapsto[(\operatorname{Tr}X)I_d-X^T]/(d-1)$. It is CPT and satisfies
--
--   $$S_{\mathrm{CB,min}}(\Phi_{\mathrm{WH}})>0,\qquad\Phi_{\mathrm{WH}}\text{ is not EBT}.$$
--
--   In particular, its output on a normalized maximally entangled input is not separable: it is supported on the antisymmetric subspace. Thus nonnegative minimal CB entropy does not characterize entanglement-breaking channels. Non-EB behavior and the entangled output are conclusions for this explicit map.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 25, §5.2: nonnegative CB entropy does not characterize EBT

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

/-- Section 5.2, PDF p.25: the explicit WH counterexample to the EBT converse.
Non-EB and survival of an entangled Choi output are conclusions, not assumptions. -/
theorem nonnegative_entropy_not_ebt (d : ℕ) [NeZero d] (hd : 3 < d) :
    let N := wernerHolevoChannel d 1
    IsChannel N ∧ 0 < minCBEntropy N ∧ ¬ IsEBT N ∧
      ¬ Entanglement.IsSeparablePositive
        (idTensorSuperop N (pureDensity (finiteMaxEntangled (Fin d)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
