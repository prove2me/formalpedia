-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_epr_ghz_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.epr_ghz_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:18:53.614995+00:00
-- url     : https://prove2.me/theorems/491d9ab2-9564-4fd5-bd7f-becdfba1ab01
-- title:
--   Theorem 5: EPR–GHZ region for isometric broadcast channels
-- statement:
--   Let $U:A'\to BC$ be a rectangular isometry on positive-dimensional finite systems. Define $Q(U)$ as the closed unassisted vanishing-error region with coordinate order $(Q,Q_B)$: tripartite Alice–Bob–Charlie GHZ ebits and independent Alice–Bob EPR ebits. A block code has one unit pure encoding and separate local CPTP decoders, applied after $U^{\otimes n}$; one joint squared-fidelity test compares the decoded state with the product of GHZ rank $\lfloor2^{nQ}\rfloor$ and EPR rank $\lfloor2^{nQ_B}\rfloor$. For the one-letter pure-ensemble output $\sigma^{TABC}=\bigoplus_t p(t)(\mathrm{id}_A\otimes\operatorname{Ad}_U)(\phi_t^{AA'})$, define the nonnegative information region by
--
--   $$Q_B\le I(A\rangle BT)_\sigma,\qquad Q\le\min\{I(T;B)_\sigma,I(T;C)_\sigma\}.$$
--
--   This region is contained in $Q(U)$, and imposing $|T|\le\min\{|A'|^2,|B|^2+|C|^2-1\}$ does not change it. The closure of its positive-blocklength rescaled union equals $Q(U)$. Entropies are in bits. This establishes the full regularized EPR–GHZ region with a joint product target, independently of two-EPR transmission.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 11, Theorem 5: EPR–GHZ region for isometric broadcast channels

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)

open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C X T E : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]

variable [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- Theorem 5, PDF pp.11–12,14. Isometric U; rate order (GHZ,EPR_B), one
joint product-target fidelity, one-letter state, cap, and closed regularization. -/
theorem epr_ghz_capacity [Nonempty A] [Nonempty B] [Nonempty C]
    (U : Matrix (B × C) A ℂ) (hU : Uᴴ * U = 1) :
    quantumInformationRegion (conjSuperop U) false ⊆ qqCapacity (conjSuperop U) ∧
    quantumInformationRegion (conjSuperop U) false = quantumInformationRegion (conjSuperop U) true ∧
    qqCapacity (conjSuperop U) = closure (regularizedQuantumRegion (conjSuperop U)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
