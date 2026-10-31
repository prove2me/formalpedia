-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P46_pureProcess_iff_unitaryProjector
-- name    : QAlgorithms.Papers.Independent.Intake100.P46.pureProcess_iff_unitaryProjector
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:01:36.48022+00:00
-- url     : https://prove2.me/theorems/c3a20029-cd51-42eb-a839-9659e7ead307
-- title:
--   Pure valid processes are unitary Choi projectors
-- statement:
--   All systems have positive finite dimensions and fixed computational bases. Choi operators are unnormalized and input first. A valid process maps every pair of local CPTP maps, with arbitrary ancillary input and output wires, to a CPTP map. Purity tests every compatible pair of local unitaries with those same ancillary extensions.
--
--   For every valid bipartite process $W$ on $P A_I A_O B_I B_O F$,
--
--   $$W\text{ is pure}\quad\Longleftrightarrow\quad \exists\,U:P\otimes A_O\otimes B_O\longrightarrow A_I\otimes B_I\otimes F\text{ unitary},\quad W=|U\rangle\!\rangle\langle\!\langle U|.$$
--
--   The displayed Choi projector is relabelled into the process wire order. The unitary satisfies both inverse equations. No equality between the total input and output dimensions is a hypothesis: existence of this unitary enforces it.
--
--   This characterizes reversible purity and includes the enlarged SWAP laboratories used in the source.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, PDF p. 3, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF pp.3–4, Theorem 2: purity iff a unitary CJ projector, for a valid process.
No global dimension equality is assumed: the existential unitary enforces it. -/
theorem pureProcess_iff_unitaryProjector {d : ProcessWireDimensions} (W : ProcessMatrix d)
    (hW : IsValidProcess W) :
    IsPureProcess W ↔ ∃ U : Matrix
      (Fin (d 1 : ℕ) × Fin (d 3 : ℕ) × Fin (d 5 : ℕ))
      (Fin (d 0 : ℕ) × Fin (d 2 : ℕ) × Fin (d 4 : ℕ)) ℂ,
      IsReversibleMatrix U ∧ W = processProjector U := by sorry

end QAlgorithms.Papers.Independent.Intake100.P46

end
