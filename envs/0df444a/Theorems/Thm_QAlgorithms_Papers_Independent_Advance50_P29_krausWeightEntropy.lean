-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_krausWeightEntropy
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.krausWeightEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:16:24.335311+00:00
-- url     : https://prove2.me/theorems/be037924-f3b0-40bb-bb7f-711fe6b86f4d
-- title:
--   §7.3: Shannon entropy of diagonal Kraus weights equals exchange entropy
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a state $\rho$, put $I(\rho,\mathcal N)=S(\mathcal N(\rho))-S_e(\rho,\mathcal N)$, where $S$ is von Neumann entropy and $S_e$ is the entropy of the reference/output state after applying $\mathcal N$ to a purification of $\rho$. Let $(A_i)_{i\in L}$ be a fixed minimal orthogonal Kraus family of a CPTP map $\mathcal N$, and put $P_i=M^{-1}\operatorname{tr}(A_i^\dagger A_i)$. Then
--
--   $$
--   P_i\ge0,\qquad\sum_iP_i=1,\qquad H(P)=S_e(\pi,\mathcal N).
--   $$
--
--   The single fixed probability vector converts typical words into typical Kraus operators.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 16, §7.3: Shannon entropy of diagonal Kraus weights equals exchange entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF p.16, §7.3: the same minimal orthogonal list defines a probability vector whose
Shannon entropy equals exchange entropy, with no input-dependent representation choice. -/
theorem krausWeightEntropy [Nonempty I] [Nonempty J] [Nonempty L]
    (A : L → Matrix J I ℂ) (hA : IsKrausFamily A) (hm : MinimalKraus A)
    (ho : ∀ i j, i ≠ j → ((A i)ᴴ * A j).trace = 0) :
    (∀ i, 0 ≤ krausWeight A i) ∧ (∑ i, krausWeight A i) = 1 ∧
    shannon (krausWeight A) = exchangeEntropy (krausApply A) (mixed I) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
