-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_noiselessPhotonZeroError
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.noiselessPhotonZeroError
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:41:55.562084+00:00
-- url     : https://prove2.me/theorems/9e93150b-1a20-4cb7-9d7c-bab88d789d45
-- title:
--   §V.2: eventual zero error for the noiseless photon channel
-- statement:
--   Consider the noiseless photon alphabet $m\mapsto|m\rangle\langle m|$ with per-word constraint $\sum_km_k\le nE$, where $E\ge0$. For every rate $R<g(E)$, there is a positive integer $n_0$ such that
--
--   $$p(n,\lceil e^{nR}\rceil)=0\qquad\text{for every }n\ge n_0.$$
--
--   Here $p$ is the optimized uniform average error under arbitrary collective bounded receivers. The statement is eventual zero error, not a claim about every short block, and concerns orthogonal photon outputs rather than coherent signals.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 28, §V.2: eventual zero error for the noiseless photon channel

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

/-- PDF p.28: the noiseless photon alphabet consists of orthogonal number
states. Zero error holds eventually at each rate below capacity, with the same
per-word number budget; it is not asserted for every short block. -/
theorem noiselessPhotonZeroError (E R : ℝ) (hE : 0 ≤ E)
    (hR : R < g E) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      cqError (photonOutput 0) (fun m => (m : ℝ)) E n (natMessagesNats n R) = 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
