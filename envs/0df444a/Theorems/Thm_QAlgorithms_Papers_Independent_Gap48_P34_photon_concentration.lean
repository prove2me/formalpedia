-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P34_photon_concentration
-- name    : QAlgorithms.Papers.Independent.Gap48.P34.photon_concentration
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:45:00.552586+00:00
-- url     : https://prove2.me/theorems/bb3af5a7-fe62-4b4e-8bdd-8776840aebec
-- title:
--   Lemma 1: uniform propagation of photon-number concentration
-- statement:
--   Fix the full-oscillator Gaussian channel $\mathcal P$, $\tau\ge0$, $\nu\ge|\tau-1|$, a finite input photon budget $N_S\ge0$, and any per-mode output slack $s>0$. Put $N_S'=\tau N_S+(\tau+\nu-1)/2$. There is a nonnegative decreasing sequence $\delta_3(n)\to0$, chosen uniformly before the input states and their tail sequence, with the following property. For every nonnegative decreasing $\delta_1(n)\to0$, every positive integer $n$, and every normalized positive trace-class state $\rho^{(n)}$ on the full n-mode Fock space satisfying $\operatorname{Tr}(\Pi_{\lceil nN_S\rceil}\rho^{(n)})\ge1-\delta_1(n)$,
--
--   $$\operatorname{Tr}\!\left(\Pi_{\lceil n(N_S'+s)\rceil}\mathcal P^{\otimes n}(\rho^{(n)})\right)\ge1-\delta_1(n)-2\sqrt{\delta_1(n)}-\delta_3(n).$$
--
--   The result propagates photon-number concentration without assuming finite mean energy or product inputs. The cutoff corrects the printed constant slack to the linear slack used by the source proof in (50)–(59). The input ceiling and finitely many small blocklengths are absorbed in the uniform remainder.
-- source:
--   Strong converse for the classical capacity of optical quantum communication channels, arXiv:1401.4161v3, PDF p. 7, Lemma 1, (33)–(64)

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

/-- Lemma 1, PDF pp.7--10, (33)--(64), with source correction:
the printed ceil(n*NSprime+delta2) is replaced by ceil(n*(NSprime+s)),
as used by the n*delta2 deviations in (50)--(59). Constant slack does not
concentrate for a nonvacuum thermal replacer. The cutoff's input ceiling
contributes less than one extra photon; positive linear slack absorbs it for
large n. Finite initial n are absorbed in delta3. Delta3 is selected before
the state and input-tail sequence, uniformly over all states at each n. -/
theorem photon_concentration (P : OpticalChannel) (NS s : ℝ)
    (hNS : 0 ≤ NS) (hs : 0 < s) :
    ∃ delta3 : ℕ → ℝ, VanishingTail delta3 ∧
      ∀ delta1 : ℕ → ℝ, VanishingTail delta1 →
        ∀ n : ℕ, 0 < n → ∀ rho : ModeState n,
          1 - delta1 n ≤ cutoffMass rho.val ⌈(n : ℝ) * NS⌉₊ →
          1 - delta1 n - 2 * Real.sqrt (delta1 n) - delta3 n ≤
            cutoffMass (P.block n rho.val) ⌈(n : ℝ) * (outputEnergy P NS + s)⌉₊ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P34

end
