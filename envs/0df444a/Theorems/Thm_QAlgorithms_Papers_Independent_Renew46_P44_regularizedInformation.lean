-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_regularizedInformation
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.regularizedInformation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:24:20.012615+00:00
-- url     : https://prove2.me/theorems/e048711a-67f7-4c78-984b-24640c3a9cab
-- title:
--   §II.2, (12)–(14): superadditivity and regularized limits
-- statement:
--   For a trace-class quantum channel $\Phi$ on a nonzero complex Hilbert space, let $C_n$ and $\bar C_n$ be the suprema of accessible information and Holevo information over all discrete ensembles of arbitrary $n$-block states, including entangled states, and collective decision rules. For positive integers $n,m$,
--
--   $$C_n+C_m\le C_{n+m},\qquad \bar C_n+\bar C_m\le\bar C_{n+m}.$$
--
--   In the extended nonnegative reals,
--
--   $$\lim_{n\to\infty}\frac{C_n}{n}=\sup_{n\ge1}\frac{C_n}{n}=C,\quad
--   \lim_{n\to\infty}\frac{\bar C_n}{n}=\sup_{n\ge1}\frac{\bar C_n}{n}=\bar C,\quad C\le\bar C.$$
--
--   No finite-capacity hypothesis is imposed. These limits define the paper's regularized information quantities.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 5, §II.2, (12)–(14): superadditivity and regularized limits

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

/-- Equations (12)-(14), PDF p.5. Limits and suprema are extended nonnegative
numbers, so neither finite-capacity assumptions nor real-supremum defaults occur. -/
theorem regularizedInformation {I : Type} [Nonempty I]
    (Phi : Matrix I I ℂ → Matrix I I ℂ) (hPhi : TC.IsTraceClassChannel Phi) :
    (∀ n m : ℕ, 0 < n → 0 < m →
      informationBlock Phi n + informationBlock Phi m ≤ informationBlock Phi (n + m) ∧
      holevoBlock Phi n + holevoBlock Phi m ≤ holevoBlock Phi (n + m)) ∧
    Tendsto (fun n : ℕ => informationBlock Phi n / (n : ℝ≥0∞))
      atTop (nhds (informationCapacity Phi)) ∧
    Tendsto (fun n : ℕ => holevoBlock Phi n / (n : ℝ≥0∞))
      atTop (nhds (regularizedChannelHolevo Phi)) ∧
    informationCapacity Phi ≤ regularizedChannelHolevo Phi := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
