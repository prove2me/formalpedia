-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_rankDeficientEncoderDependence
-- name    : QAlgorithms.Papers.Independent.Information100.P22.rankDeficientEncoderDependence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:00:24.697183+00:00
-- url     : https://prove2.me/theorems/65008608-126c-420c-9b9c-15b06b1a4681
-- title:
--   Observation 3: Rank-deficient exact recovery and encoder dependence
-- statement:
--   Fix $m=3$, $k=1$, $A_S=A_N=0$ and
--   $$B=\begin{pmatrix}1&0&0\\0&1&0\\1&1&0\end{pmatrix}.$$
--   This same graph resource has cut rank and signal entropy both equal to $2$. Both YZ and ZY encoders allow exact recovery of the complete input from every prescribed $S_iN$, with uniform individual concealment; both XZ and ZX encoders fail all-output exact recovery. The graph, cut and Pauli frame remain fixed. This attains the architecture-independent entanglement floor.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 12, Observation 3: Rank-deficient exact recovery and encoder dependence

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Observation 3, PDF p.12, proof pp.39–40. Keep the graph, cut, and frame fixed. -/
theorem rankDeficientEncoderDependence :
    rankTwoExample.B.rank = 2 ∧
    vnEntropy (rhoS (graphVector rankTwoExample)) = 2 ∧
    (∀ P Q, classYZ P Q → AllRecoverable (graphVector rankTwoExample) (twoPauliEncoder 3 1 P Q) ∧
      UniformlyConcealed (graphVector rankTwoExample) (twoPauliEncoder 3 1 P Q)) ∧
    (∀ P Q, classXZ P Q → ¬ AllRecoverable (graphVector rankTwoExample) (twoPauliEncoder 3 1 P Q)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
