-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_pbt_transpositionConstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.pbt_transpositionConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:43:25.135382+00:00
-- url     : https://prove2.me/theorems/0ae8b32c-49e8-43bf-9322-f79dbd3b12bc
-- title:
--   §7: deterministic PBT adaptation
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For each $d\ge1$ and $k\ge1$, there is an optimal deterministic $k$-port teleportation protocol with a unit resource $|\phi\rangle$ on $A_1\cdots A_kB_1\cdots B_k$ and a normalized $k$-outcome POVM, whose resource obeys $(U^{\otimes k}\otimes I)|\phi\rangle=(I\otimes(U^T)^{\otimes k})|\phi\rangle$. Construct $S_{\rm PBT}$ by querying the $A$ halves in parallel, measuring the target together with the queried outputs, and retaining the unqueried $B$ port selected by the outcome, discarding the others. This explicit circuit is parallel and
--   $$\overline F(S_{\rm PBT},U\mapsto U^T)=F_{\rm ent}^*(\mathrm{PBT};d,k).$$
--   Here the right side is the maximum channel fidelity of the teleportation channel with the identity. The linked channel is also explicitly the POVM-and-selected-port channel of the queried resource. The measured/retained halves correct the source's reversed decoder labels using Eq.(70). The operational circuit is not claimed to be measure-and-prepare: at one port its Bell-resource process is entangled across the tester/output partition.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 24, §7: deterministic PBT adaptation

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P06

namespace QAlgorithms.Papers.Independent.Extend50.P06

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

-- Exact accepted interfaces; no duplicate SU subtype or ambient-coordinate Haar law.

open QAlgorithms.Papers.Independent.Information100.P47 (Mat)

open QAlgorithms.Papers.Independent.Claimed50.P21 (SU HaarLaw)

open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P06.targetMatrixMeasurable

/-- PDF p.24, §7: optimal deterministic PBT adapts to a parallel circuit with
identical average entanglement fidelity. Printed “measure auxiliaries” is
changed to measuring the queried outputs and retaining the unqueried port,
as required by Eq.(70). This is an operational construction, not an assumed
tester. The printed measure-and-prepare label is also corrected: already at
k=1,d≥2, covariance forces a Bell resource and the sole effect is identity,
so this process contains an entangled IF factor across IO|PF and is not a
measure-and-prepare process in Definition 5. -/
theorem pbt_transpositionConstruction (d k : ℕ) (hd : 0 < d) (hk : 1 ≤ k)
    (H : HaarLaw d) :
    ∃ P : PBTProtocol k d, PBTCovariant P ∧ IsGreatest (pbtScores k d) (pbtScore P) ∧
      TransformationAdmissible .parallel (pbtProcess P) ∧
      (∀ U : SU d, insertSlots (pbtProcess P) (unitarySlots U.val) =
        pbtChoi P (queriedResource P U.val)) ∧
      transformationAverage H transposeTarget (pbtProcess P) = pbtScore P := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
