-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_classical_capacity_coherent_optimizer
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.classical_capacity_coherent_optimizer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:42:20.346732+00:00
-- url     : https://prove2.me/theorems/fbce8dad-9b0d-47f4-a5f3-c390f02f9a8b
-- title:
--   Exact classical capacity and coherent attainment
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. Let $p\in[0,1]$ be the prior of the first channel and $1-p$ that of the second, and let $n\geq0$. Put
--
--   $$\xi(n)=\frac{1+\sqrt{1-4p(1-p)\left(1-e^{-n(\sqrt{\kappa_1}-\sqrt{\kappa_0})^2}\right)}}2.$$
--
--   Writing $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, the capacity optimized over all classical transmitters is
--
--   $$C_c(\widetilde\Phi\mid n)=h_2(\xi(n))=\chi(\widetilde\Phi\mid|\sqrt n\rangle\langle\sqrt n|).$$
--
--   The displayed coherent state is a normalized classical input with one signal and no reference and has exact energy $n$. Moreover $n\mapsto h_2(\xi(n))$ is concave on $[0,\infty)$. This gives an optimal value and an attaining transmitter, including $n=0$ and degenerate priors.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 10, Theorem 1: exact classical reading capacity and a coherent optimizer

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P35

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter tensorApply traceSize)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedRelativeEntropyNats binaryEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 1 and its proof, PDF pp.10--11, (66)--(73): exact classical
optimum, coherent attainment, and concavity. Endpoint priors and n=0 are allowed. -/
theorem classical_capacity_coherent_optimizer (M : LossMemory) (n : ℝ) (hn : 0 ≤ n) :
    classicalReadingCapacity M n = ENNReal.ofReal (classicalFormula M n) ∧
      IsDensity (coherentInput n) ∧ IsClassicalCellTransmitter (coherentInput n) ∧
      signalEnergy (coherentInput n) = ENNReal.ofReal n ∧
      lossInformation M.kappa0 M.kappa1 M.p (coherentInput n) = classicalReadingCapacity M n ∧
      ConcaveOn ℝ (Set.Ici 0) (classicalFormula M) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
