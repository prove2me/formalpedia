-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_ot_senderSecurity
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.ot_senderSecurity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:21:55.253121+00:00
-- url     : https://prove2.me/theorems/2c7890a5-9893-48d5-8333-27fb5415ac1e
-- title:
--   Theorem 4.6: bounded-storage sender security of concrete OT
-- statement:
--   Let $\ell(n),q(n)$ be nonnegative integer sequences. Suppose there are $a>0$ and $N$ such that for every $n\ge N$,
--   $$an\le n/4-2\ell(n)-q(n).$$
--   There is a nonnegative negligible function $\varepsilon(n)$, uniform over all hash families and receiver attacks, such that Figure 1 has perfect honest correctness and is $\varepsilon(n)$-sender-secure. Specifically, for every receiver attack there is a classical binary extension $C'$ preserving its final output state, for which
--   $$\delta\!\left(\rho_{S_{1-C'}S_{C'}C'\widetilde R},2^{-\ell(n)}I\otimes\rho_{S_{C'}C'\widetilde R}\right)\le\varepsilon(n).$$
--   Only the coherent memory immediately before step 3 is bounded by $q(n)$ qubits. Classical storage and computation are unrestricted, and quantum storage after revelation is unrestricted. The final view includes the whole public transcript. Negligible means decay faster than every inverse polynomial.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 11, Theorem 4.6: bounded-storage sender security of concrete OT

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Theorem 4.6, p.11: one negligible epsilon works before quantifying over
ANY attacks, hash families, classical information, and final quantum memory. -/
theorem ot_senderSecurity (ell q : ℕ → ℕ) (hslack : OTLinearSlack 2 ell q) :
    ∃ epsilon : ℕ → ℝ, Negligible epsilon ∧
      ∀ n, HonestOTCorrect n (ell n) ∧ OTSenderSecure n (ell n) (q n) (epsilon n) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
