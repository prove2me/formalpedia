-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactBobQuestionMass_eq_jointPrefixQuestionMass
-- name    : QuantumParallelRepetition.exactBobQuestionMass_eq_jointPrefixQuestionMass
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T08:29:02.130225+00:00
-- url     : https://prove2.me/theorems/32b53aaf-52d7-4658-8254-c00df50e8678
-- title:
--   Bob's question mass equals the joint prefix question mass with his distinguished question pinned
-- statement:
--   In the same setting, Bob's question mass at a history $h$ and a value $y\in Y$ is
--   $$m_B(h,y)=\sum_{q'}\mathbf 1\big[\,c(q')=h\ \text{and}\ y'_i=y\,\big]\,\pi_n(q'),$$
--   the prior probability that the revealed history is $h$ and that Bob's question at the marked coordinate $i$ equals $y$; and $Z(F_X,F_Y;q)$ denotes, as before, the total prior weight of the question pairs agreeing with $q$ on the $X$-coordinates in $F_X$ and on the $Y$-coordinates in $F_Y$. The theorem states that for every question pair $q$,
--   $$m_B\big(c(q),\,y_i\big)\;=\;Z\big(M_A,\,M_B\cup\{i\};\,q\big),$$
--   with $M_A$ and $M_B$ the seed's fair masks. This is the exact mirror of the Alice-side identity: revealing the history and additionally Bob's own question at the marked coordinate is the same as pinning Alice's questions on $M_A$ and Bob's on $M_B\cup\{i\}$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L37246-L37306

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactBobQuestionMass_eq_jointPrefixQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) :
    exactBobQuestionMass G n D seed
        (exactRevealCode D seed q)
        (q.2 seed.coordinate.val) =
      exactJointPrefixQuestionMass G n
        (exactFairAliceQuestionMask D seed)
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed)) q.1 q.2 := by sorry
