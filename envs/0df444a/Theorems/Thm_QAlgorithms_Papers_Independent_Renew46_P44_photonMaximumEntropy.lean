-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_photonMaximumEntropy
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.photonMaximumEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:36:50.693129+00:00
-- url     : https://prove2.me/theorems/bc7cbe73-4def-476f-a9d5-24d27bd45087
-- title:
--   Lemma 1: maximum entropy at a photon-number bound
-- statement:
--   On the full single-mode Fock space, let $N\ge0$ and let
--
--   $$\tau_N=\frac1{N+1}\sum_{j=0}^\infty\left(\frac N{N+1}\right)^j|j\rangle\langle j|,\qquad
--   g(N)=(N+1)\log(N+1)-N\log N.$$
--
--   The operator is a normalized trace-class density of mean photon number $N$, and
--
--   $$H(\tau_N)=g(N),\qquad \operatorname{Tr}(Sa^\dagger a)\le N\ \Longrightarrow\ H(S)\le H(\tau_N)$$
--
--   for every positive trace-class density $S$. Neither finite entropy nor finite support of $S$ is assumed. Extended photon moments exclude divergent-series defaults. At $N=0$, the maximum is attained by the vacuum and $g(0)=0$.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 24, Lemma 1: maximum entropy at a photon-number bound

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 1, PDF p.24, (84)-(86). All positive trace-class densities are
included; finite entropy is a conclusion. N=0 is the attained vacuum maximum. -/
theorem photonMaximumEntropy (N : ℝ) (hN : 0 ≤ N) :
    F.ThermalRealized (2 * N + 1) ∧
    numberMean (F.thermalDensity (2 * N + 1)) = ENNReal.ofReal N ∧
    QAlgorithms.Papers.Independent.Claimed50.P39.fockEntropyNats
      (F.thermalDensity (2 * N + 1)) = ENNReal.ofReal (g N) ∧
    ∀ S : F.FockOperator, F.IsDensity S → numberMean S ≤ ENNReal.ofReal N →
      QAlgorithms.Papers.Independent.Claimed50.P39.fockEntropyNats S ≤
        QAlgorithms.Papers.Independent.Claimed50.P39.fockEntropyNats
          (F.thermalDensity (2 * N + 1)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
