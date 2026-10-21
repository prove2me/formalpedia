-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_operationalTimeSharing
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.operationalTimeSharing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:04:27.730567+00:00
-- url     : https://prove2.me/theorems/e8838832-7a03-4c33-9660-0fe92141200e
-- title:
--   §2: operational time-sharing and convexity
-- statement:
--   Let $\mathcal N$ be a channel between finite nonzero registers and let $s$ be either entanglement transmission (Ib) or entanglement generation (II), without auxiliary communication or preshared entanglement. Suppose positive integer block lengths $n_1,n_2$ admit codes with respective message dimensions $m_1,m_2$, logical dimensions $k_1,k_2$, and both per-message errors at most $\epsilon>0$. Quantum errors use squared fidelity. There is a code in the same scenario with
--
--   $$
--   n=n_1+n_2,\qquad m=m_1m_2,\qquad k=k_1k_2,\qquad
--   \text{both errors}\leq2\epsilon.
--   $$
--
--   Consequently, writing $v_i=(\log_2m_i/n_i,\log_2k_i/n_i)$, its rate pair is $\lambda v_1+(1-\lambda)v_2$, where $\lambda=n_1/(n_1+n_2)$. The two operational capacity regions are convex:
--
--   $$
--   S_{\mathrm{Ib}}(\mathcal N)\text{ and }S_{\mathrm{II}}(\mathcal N)\text{ are convex}.
--   $$
--
--   Integer block lengths implement rounded time-sharing. This operational concatenation is distinct from convexity of the single-letter entropy region.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 4, §2: operational time-sharing and convexity

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Section 2, PDF p.4: finite-code concatenation and the convexity it implies.
Positive integer block lengths express the source's rounded lambda*n notation;
the sizes multiply, hence logarithmic rates have weights n1/(n1+n2), n2/(n1+n2).
Errors add. Appendix A's single-letter convexity is a separate statement. -/
theorem operationalTimeSharing
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    (∀ s : Scenario, (s = .Ib ∨ s = .II) →
      ∀ n1 n2 : ℕ, 0 < n1 → 0 < n2 → ∀ epsilon : ℝ, 0 < epsilon →
        ∀ m1 k1 m2 k2 : ℕ,
          HasCode s N n1 epsilon m1 k1 → HasCode s N n2 epsilon m2 k2 →
          HasCode s N (n1 + n2) (2 * epsilon) (m1 * m2) (k1 * k2)) ∧
    Convex ℝ (simultaneousOperationalRegion .Ib N) ∧ Convex ℝ (simultaneousOperationalRegion .II N) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
