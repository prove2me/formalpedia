-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P28_constrainedClassicalCapacityPipelining
-- name    : QAlgorithms.Papers.Independent.Bridge50.P28.constrainedClassicalCapacityPipelining
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:27:31.628979+00:00
-- url     : https://prove2.me/theorems/dfd03d05-26ce-4882-82e3-bf2b51ed6654
-- title:
--   Unnumbered pipelining property for constrained classical capacity
-- statement:
--   Let $\mathcal E_2:A\to B$ and $\mathcal E_1:B\to C$ be trace-class completely positive trace-preserving quantum channels on nonempty countable Hilbert bases. Fix a nonnegative integer-valued input energy weight $w$ on $A$ and a finite mean input budget $N\ge0$. Define the unassisted classical capacity using arbitrary mixed block signals, one collective decoder, vanishing uniform-message average error, and uniform-message average block energy at most $nN$. Both capacities use exactly the same input energy observable and budget. Then
--
--   $$
--   C_{N,w}(\mathcal E_1\circ\mathcal E_2)\le C_{N,w}(\mathcal E_2).
--   $$
--
--   Receiver postprocessing cannot increase this capacity. No energy constraint is imposed on the intermediate or final output. For the paper's oscillator, $w(j)=j$ is the photon-number weight.
-- source:
--   The classical capacity of quantum thermal noise channels to within 1.45 bits, arXiv:1207.0256v1, PDF p. 1, Unnumbered pipelining property for constrained classical capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P28

open Filter

open scoped BigOperators NNReal ENNReal Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (traceClassChannelPower tracePair)

open QAlgorithms.Papers.Independent.Gap48.P26 (weightedPhotonExpectation)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Unnumbered pipelining property, PDF pp.1--2: free receiver postprocessing.
The SAME input weight and budget are used on both sides; E1's input and output
energy are unrestricted. Channels are genuine trace-class CPTP maps. -/
theorem constrainedClassicalCapacityPipelining
    {I J K : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (weight : I → ℕ) (N : ℝ) (hN : 0 ≤ N)
    (E1 : Matrix J J ℂ → Matrix K K ℂ)
    (E2 : Matrix I I ℂ → Matrix J J ℂ)
    (hE1 : IsTraceClassChannel E1) (hE2 : IsTraceClassChannel E2) :
    classicalPhotonCapacityBits weight (E1 ∘ E2) N ≤
      classicalPhotonCapacityBits weight E2 N := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P28

end
