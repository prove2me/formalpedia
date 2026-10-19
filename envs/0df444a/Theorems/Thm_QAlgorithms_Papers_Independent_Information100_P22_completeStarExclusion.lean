-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_completeStarExclusion
-- name    : QAlgorithms.Papers.Independent.Information100.P22.completeStarExclusion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:12:11.176071+00:00
-- url     : https://prove2.me/theorems/179af4e2-d181-4bbd-9a5d-e3da705b0351
-- title:
--   §V C / S4.1, unnumbered: complete and star graphs excluded
-- statement:
--   Let $m\ge2$, $k\ge1$, and consider the complete graph or star on $2mk$ vertices. For every oriented balanced cut and every sector assignment,
--   $$\operatorname{rank}_{\mathbb F_2}B=1,$$
--   and no ordered distinct two-Pauli encoder permits exact recovery from every prescribed $S_iN$. The universal exclusion includes all frames and factorizations in this regime. It is a family statement rather than an extrapolation of the 24-qubit example.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 14, §V C / S4.1, unnumbered: complete and star graphs excluded

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- §V C / S4.1, PDF pp.14,39: rank one across every balanced cut and universal fixed-encoder exclusion. -/
theorem completeStarExclusion (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (G : LabeledGraph (Fin (2*(m*k)))) (hG : G = completeGraph (m*k) ∨ G = starGraph (m*k)) :
    ∀ e : (Wires m k ⊕ Wires m k) ≃ Fin (2*(m*k)),
      (realize G e).B.rank = 1 ∧ ∀ P Q : Axis, P ≠ Q →
        ¬ AllRecoverable (graphVector (realize G e)) (twoPauliEncoder m k P Q) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
