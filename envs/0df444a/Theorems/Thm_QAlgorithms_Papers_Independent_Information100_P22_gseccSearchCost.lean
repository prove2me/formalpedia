-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_gseccSearchCost
-- name    : QAlgorithms.Papers.Independent.Information100.P22.gseccSearchCost
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:09:41.116276+00:00
-- url     : https://prove2.me/theorems/99a089ed-515c-470a-9673-9f23ae25276a
-- title:
--   §IV A / Eq.(S42), unnumbered: certification search cost
-- statement:
--   There are fixed uniform RAM programs for fixed-cut and exhaustive graph-level certification, and constants $C>0$ and $N_0$, chosen before all sizes, axes and graphs, such that for $\nu=mk\ge N_0$, $m\ge2$, $k\ge1$, they return the correct accept/reject decision within respectively
--   $$C\nu^3\quad\text{and}\quad C\binom{2\nu}{\nu}\nu^3$$
--   charged machine transitions. Inputs contain the size, axes and complete binary adjacency data. The fixed-cut decision allows a compatible sector assignment; graph-level acceptance ranges over all balanced oriented cuts. The accepted word-machine semantics charges arithmetic, memory access and branching; divergence cannot satisfy the halting bound. This is an exhaustive algorithm upper bound, not hardness or a complexity-class claim.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 10, §IV A / Eq.(S42), unnumbered: certification search cost

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eq.(S42), PDF pp.10,34: actual uniform RAM programs, with constants before all graph inputs.
The accepted unit-cost word machine charges each binary arithmetic/access/branch step. -/
theorem gseccSearchCost :
    ∃ fixedProgram graphProgram : QAlgorithms.ExpanderCodes.DecoderImplementation,
      ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ m k : ℕ, 2 ≤ m → 1 ≤ k → N0 ≤ m*k →
        ∀ P Q : Axis, P ≠ Q →
          (∀ G : CutGraph (Fin (m*k)), ∃ t : ℕ,
            (QAlgorithms.ExpanderCodes.decoderExecution fixedProgram (fixedCutInput P Q G) t).halted =
              some (decide (FixedCutAdmissible (m := m) (k := k) P Q G)) ∧
            (t : ℝ) ≤ C*((m*k : ℕ) : ℝ)^3) ∧
          (∀ G : LabeledGraph (Fin (2*(m*k))), ∃ t : ℕ,
            (QAlgorithms.ExpanderCodes.decoderExecution graphProgram (graphInput P Q G) t).halted =
              some (decide (GSECC (m := m) (k := k) P Q G)) ∧
            (t : ℝ) ≤ C*(Nat.choose (2*(m*k)) (m*k) : ℝ)*((m*k : ℕ) : ℝ)^3) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
