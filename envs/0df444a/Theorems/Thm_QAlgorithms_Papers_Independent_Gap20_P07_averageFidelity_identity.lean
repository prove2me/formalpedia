-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_averageFidelity_identity
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.averageFidelity_identity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:20:44.467024+00:00
-- url     : https://prove2.me/theorems/92d4c079-b167-4182-ae90-8b10f0f1826c
-- title:
--   Proposition 4.4 / (44): average fidelity and channel fidelity
-- statement:
--   Let $T$ be a CPTP endomorphism on a complex system of integer dimension $d\ge1$. Let $F_{\rm av}(T)$ be its normalized Haar average squared pure-state survival fidelity and $F_c(T)$ its squared maximally entangled overlap, equivalently entanglement fidelity of the maximally mixed input. Then
--   $$F_{\rm av}(T)=\frac{dF_c(T)+1}{d+1}.$$
--   This exact identity holds in every positive dimension, including $d=1$, and relates the two mean fidelity criteria.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 14, Proposition 4.4 / (44): average fidelity and channel fidelity

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

/-- PDF pp.14--16, Proposition 4.4, (44): positive arbitrary finite dimension,
normalized Haar average and squared maximally entangled overlap. -/
theorem averageFidelity_identity (d : ℕ) (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    QuditFidelity.averageFidelity d hd T =
      ((d : ℝ) * QuditFidelity.entanglementFidelity d hd T + 1) / (d + 1 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
