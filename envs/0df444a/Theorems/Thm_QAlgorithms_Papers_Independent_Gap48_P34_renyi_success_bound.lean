-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P34_renyi_success_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P34.renyi_success_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:45:44.296384+00:00
-- url     : https://prove2.me/theorems/5274489f-cb4a-4a4d-9117-a6d339765349
-- title:
--   Theorem 1: finite-block Renyi success bound
-- statement:
--   Let $\mathcal P$ be the centered full-oscillator phase-insensitive Gaussian channel with $\tau\ge0$, $\nu\ge|\tau-1|$, and let $N_S\ge0$. Set $N_B'=(\tau+\nu-1)/2$, $N_S'=\tau N_S+N_B'$, and use bit-valued thermal entropy $g$. For each entropy slack $d>0$ there is a nonnegative decreasing sequence $\delta_3(n)\to0$, uniform over all codes, tail sequences, Renyi orders, and smoothing parameters. Let $\delta_1(n)\to0$ be nonnegative and decreasing, and let an arbitrary unassisted positive-blocklength $n$ code have $M\ge1$ uniform messages, normalized full-Fock codewords and normalized collective decoding POVM, with average retained input mass at least $1-\delta_1(n)$ at cutoff $\lceil nN_S\rceil$. Write $R_n=\log_2 M/n$, $h_\alpha(x)=\log_2((x+1)^\alpha-x^\alpha)/(\alpha-1)$, and $e_n=2\sqrt{\delta_1(n)+2\sqrt{\delta_1(n)}+\delta_3(n)}$. For every $\alpha>1$ and $0<\varepsilon<1$,
--
--   $$p_{\rm succ}\le2^{-nR_n}\,2^{\,n[g(N_S')-h_\alpha(N_B')+d]+\log_2(1/\varepsilon)/(\alpha-1)}+\varepsilon+e_n.$$
--
--   The vacuum-output entropy is written in its exact thermal form. Continuity absorbs the positive photon slack into $d$; the rank overhead is absorbed for sufficiently large blocklength, with $\delta_3$ enlarged on the finite initial segment. Thus no missing finite-size rank term is silently set to zero.
-- source:
--   Strong converse for the classical capacity of optical quantum communication channels, arXiv:1401.4161v3, PDF p. 10, Theorem 1, (65)

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

/-- Theorem 1, PDF p.10, (65), and pp.11--12, (67)--(76).
The exact vacuum Renyi entropy is substituted using (79).
Entropy slack d absorbs a strictly smaller positive photon slack by continuity
of g, as well as the finite-size rank remainder in (31). Delta3 is enlarged
on a finite initial segment, giving an all-positive-n version without dropping
finite-size overhead. Neither concentration nor Gaussian optimizer additivity
is assumed. The nested root is exactly the PDF rendering of (65),(67). -/
theorem renyi_success_bound (P : OpticalChannel) (NS d : ℝ)
    (hNS : 0 ≤ NS) (hd : 0 < d) :
    ∃ delta3 : ℕ → ℝ, VanishingTail delta3 ∧
      ∀ delta1 : ℕ → ℝ, VanishingTail delta1 →
        ∀ n : ℕ, 0 < n → ∀ C : OpticalCode n,
          photonOccupationConstraint C NS (delta1 n) →
          ∀ alpha : ℝ, 1 < alpha → ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
            successProbability P C ≤
              (2 : ℝ) ^ (-(n : ℝ) * codeRate (C.messages - 1) n) *
                (2 : ℝ) ^ ((n : ℝ) *
                  (thermalEntropy (outputEnergy P NS) - thermalRenyi alpha (noiseEnergy P) + d) +
                    logBits (1 / epsilon) / (alpha - 1)) +
              epsilon + gentleError (delta1 n) (delta3 n) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P34

end
