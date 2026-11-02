-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_announcementReduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.announcementReduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:37:13.408223+00:00
-- url     : https://prove2.me/theorems/bcbcf860-0572-4824-8ff8-67cf91c32125
-- title:
--   II: accepting several partition cells cannot help when each cell is extendable
-- statement:
--   Let $n\ge1$ and $0\le Q\le\tfrac12$. Partition the binary words of length $n$ into finitely many nonempty disjoint cells $C_s$, and let $S_0$ be a nonempty set of accepted cells. For each cell, form its Bob-only filtered operator $P_s$ from the six-state input, labeling its distinct words individually. Let $\Omega$ be the accepted announcement operator with the cell label recorded classically by both parties, and let $\bar\Omega$ be obtained by forgetting this label. These are block-diagonal sums of branches, without coherence between different announcements. With $\mathrm{Ext}_B$ denoting positive-operator symmetric extendability to a copy of Bob,
--
--   $$\bigl[\forall s\in S_0,\ \mathrm{Ext}_B(P_s)\bigr]
--   \Longrightarrow \mathrm{Ext}_B(\Omega)\ \text{and}\ \mathrm{Ext}_B(\bar\Omega).$$
--
--   Equivalently, a nonextendable accepted public announcement has a nonextendable cell branch. This justifies reducing the partition search to single accepted cells; it makes no claim that nonextendability suffices to distill key.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 3, II: accepting several partition cells cannot help when each cell is extendable

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.3: accepting several partition cells cannot help if every accepted
single-cell branch is extendable. No sufficiency claim for key distillation. -/
theorem announcementReduction {n : ℕ} (hn : 1 ≤ n)
    {S : Type} [Fintype S] [Nonempty S]
    (cells : S → Finset (Qubits n)) (hcells : ∀ s, (cells s).Nonempty)
    (hpartition : ∀ w : Qubits n, ∃! s, w ∈ cells s)
    (accepted : Finset S) (ha : accepted.Nonempty)
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1 / 2) :
    ((∀ s ∈ accepted,
      BobExtendible (bobState (fun w : {w : Qubits n // w ∈ cells s} => w.val) Q)) →
      BobExtendible (publicAnnouncement cells accepted Q) ∧
      BobExtendible (forgottenAnnouncement cells accepted Q)) ∧
    (¬ BobExtendible (publicAnnouncement cells accepted Q) →
      ∃ s ∈ accepted,
        ¬ BobExtendible (bobState (fun w : {w : Qubits n // w ∈ cells s} => w.val) Q)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
