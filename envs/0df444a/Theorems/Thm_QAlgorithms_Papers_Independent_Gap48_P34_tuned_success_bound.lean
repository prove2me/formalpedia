-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P34_tuned_success_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P34.tuned_success_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:46:43.276748+00:00
-- url     : https://prove2.me/theorems/97f4747d-5a22-418b-a311-9367bf04027b
-- title:
--   Corollary 1: tuned success bound and strong converse
-- statement:
--   Let $\mathcal P$, $N_S\ge0$, $N_B'=(\tau+\nu-1)/2$, and $N_S'=\tau N_S+N_B'$ be as above, with all entropies in bits. Define $A(x)=(x+1)^{3/2}-x^{3/2}$, $B(x)=\sqrt{x+1}-\sqrt{x}$, $v(x)=A(x)^2+B(x)^{-2}+1$, and $K(x)=4[\log_2 v(x)]^2$. There is a radius $r>0$ such that, for each entropy slack $d>0$, one can choose a nonnegative decreasing $\delta_3(n)\to0$ uniformly over all $0<d_4<r$, $d_5>0$, codes and input tails. For any nonnegative decreasing $\delta_1(n)\to0$ and any normalized full-Fock unassisted n-use code with positive message count, uniform messages, collective POVM, and average cutoff mass at least $1-\delta_1(n)$, put $R_n=\log_2 M/n$ and $e_n=2\sqrt{\delta_1(n)+2\sqrt{\delta_1(n)}+\delta_3(n)}$. Then
--
--   $$p_{\rm succ}\le2^{-nR_n}\,2^{\,n[g(N_S')-g(N_B')+d+d_5/d_4+d_4K(N_B')]}+2^{-nd_5}+e_n.$$
--
--   For every fixed $R>g(N_S')-g(N_B')$, every such code family whose rates are eventually at least $R$ has success tending to zero. The parameters can be tuned so that the three exponent slack terms are smaller than the rate gap. The finite inequality itself needs no smallness condition on $d_5/d_4$. The source's conservative $K$ is retained without asserting its erroneous intermediate equality (84) with (81).
-- source:
--   Strong converse for the classical capacity of optical quantum communication channels, arXiv:1401.4161v3, PDF p. 12, Corollary 1, (77)–(87)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P34

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Renew46.P30
  (HilbertDensity nuclearExpansionTrace mixedLikelihood
   TraceClassCPTP multiKet multiDisplacement)

open QAlgorithms.Papers.Independent.Claimed50.P30 (ModeOperator)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P08 (codeRate)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Corollary 1, PDF pp.12--13, (77)--(87): the tuned finite-block bound
AND the operational convergence conclusion. Alpha=1+d4 is restricted to an
existential neighborhood of one. No invented neighborhood size is imposed.
The printed K from (84),(87) is a conservative bound; (84) is NOT asserted
equal to (81). Here d is an entropy slack, not the photon slack of Lemma 1.
Delta5/delta4 need not be small for the finite inequality. For convergence,
they can be chosen successively small relative to any positive rate gap. -/
theorem tuned_success_bound (P : OpticalChannel) (NS : ℝ) (hNS : 0 ≤ NS) :
    (∃ radius : ℝ, 0 < radius ∧
      ∀ d : ℝ, 0 < d → ∃ delta3 : ℕ → ℝ, VanishingTail delta3 ∧
        ∀ d4 : ℝ, 0 < d4 → d4 < radius →
          ∀ d5 : ℝ, 0 < d5 →
            ∀ delta1 : ℕ → ℝ, VanishingTail delta1 →
              ∀ n : ℕ, 0 < n → ∀ C : OpticalCode n,
                photonOccupationConstraint C NS (delta1 n) →
                successProbability P C ≤
                  (2 : ℝ) ^ (-(n : ℝ) * codeRate (C.messages - 1) n) *
                    (2 : ℝ) ^ ((n : ℝ) *
                      (thermalEntropy (outputEnergy P NS) - thermalEntropy (noiseEnergy P) +
                        d + d5 / d4 + d4 * renyiK (noiseEnergy P))) +
                  (2 : ℝ) ^ (-(n : ℝ) * d5) + gentleError (delta1 n) (delta3 n)) ∧
    StrongConverseAt P NS
      (thermalEntropy (outputEnergy P NS) - thermalEntropy (noiseEnergy P)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P34

end
