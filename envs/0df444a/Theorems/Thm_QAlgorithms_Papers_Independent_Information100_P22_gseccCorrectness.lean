-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_gseccCorrectness
-- name    : QAlgorithms.Papers.Independent.Information100.P22.gseccCorrectness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:08:32.542639+00:00
-- url     : https://prove2.me/theorems/53b87768-7846-4994-bbc3-c9a2773304cd
-- title:
--   §IV A / S3.1, unnumbered: exact graph-level certification
-- statement:
--   Fix $m\ge2$, $k\ge1$, distinct ordered axes, and a labeled simple graph $G$ on $2mk$ vertices. GSECC accepts if some oriented balanced cut with a sector decomposition satisfies its exact kernel inclusion. Then
--   $$\mathrm{GSECC}(G)=\mathrm{valid}\iff\exists\text{ such cut and sectors admitting all-output exact recovery and uniform concealment}.$$
--   A realization is encoded by a bijection from labeled signal and key wires to graph vertices. The same witness specifies the prescribed outputs. Failure of a single cut or partition never establishes graph-level invalidity.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 9, §IV A / S3.1, unnumbered: exact graph-level certification

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- §IV A / S3.1, PDF pp.9–10,33–34: exact graph-level certification and recovery witnesses. -/
theorem gseccCorrectness (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) (P Q : Axis) (hPQ : P ≠ Q)
    (G : LabeledGraph (Fin (2*(m*k)))) :
    GSECC (m := m) (k := k) P Q G ↔
      ∃ e : (Wires m k ⊕ Wires m k) ≃ Fin (2*(m*k)),
        AllRecoverable (graphVector (realize G e)) (twoPauliEncoder m k P Q) ∧
        UniformlyConcealed (graphVector (realize G e)) (twoPauliEncoder m k P Q) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
