-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_subexponentialSequence_extension
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.subexponentialSequence_extension
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:27:20.373424+00:00
-- url     : https://prove2.me/theorems/5ae19e0b-014d-48a3-acb2-744362c86f35
-- title:
--   Lemma 7.1: extending subexponential coding sequences
-- statement:
--   Let $\Delta$ be a finite nonnegative function on pairs of positive integers, decreasing in its first argument and increasing in its second. Suppose $N_\mu\to\infty$, $N_{\mu+1}/N_\mu\to1$, and $\Delta(N_\mu,M_\mu)\to0$. For any positive sequences $n_\nu,m_\nu$ with $n_\nu\to\infty$ and
--   $$\limsup_\nu\frac{m_\nu}{n_\nu}<\liminf_\mu\frac{M_\mu}{N_\mu},$$
--   one has $\Delta(n_\nu,m_\nu)\to0$. Rate limits are interpreted in the extended nonnegative reals. No monotonicity of the sequence $N_\mu$ itself is assumed. This extends reliable subexponential code sequences using only resource wasting.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 26, Lemma 7.1: extending subexponential coding sequences

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)

open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)

/-- PDF pp.26--27, Lemma 7.1: subexponential means divergence AND successive
ratio tending to one; the rate comparison is strict limsup < liminf. Extended
rate limits retain unbounded rates; the error itself is finite nonnegative. -/
theorem subexponentialSequence_extension (delta : ℕ+ → ℕ+ → ℝ≥0)
    (hmono : ErrorMonotone (fun n m => (delta n m : ℝ≥0∞)))
    (N M : ℕ → ℕ+)
    (hN : Tendsto (fun a => (N a : ℕ)) atTop atTop)
    (hratio : Tendsto (fun a => (N (a + 1) : ℝ) / (N a : ℝ)) atTop (𝓝 1))
    (herror : Tendsto (fun a => delta (N a) (M a)) atTop (𝓝 0))
    (n m : ℕ → ℕ+) (hn : Tendsto (fun a => (n a : ℕ)) atTop atTop)
    (hrate : Filter.limsup (rateRatio n m) atTop < Filter.liminf (rateRatio N M) atTop) :
    Tendsto (fun a => delta (n a) (m a)) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
