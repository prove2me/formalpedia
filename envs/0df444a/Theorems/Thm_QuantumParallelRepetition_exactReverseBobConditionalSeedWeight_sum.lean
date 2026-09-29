-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseBobConditionalSeedWeight_sum
-- name    : QuantumParallelRepetition.exactReverseBobConditionalSeedWeight_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T05:40:55.239412+00:00
-- url     : https://prove2.me/theorems/b70361c9-5e64-4ee7-b195-153a08ab60b3
-- title:
--   Conditioning the seed law on Bob's side gives a probability distribution
-- statement:
--   Recall that a *seed* over a finite type $M$ is a tuple $\sigma=(i,\pi,\tau_L,\tau_R,\ell,r)$ consisting of a marked coordinate $i\in M$, a two-colouring $\pi:M\to\{0,1\}$, orderings $\tau_L,\tau_R$ of the two colour classes $L(\sigma)=\{j\neq i:\pi(j)=0\}$ and $R(\sigma)=\{j\neq i:\pi(j)=1\}$, and cut positions $\ell\in\{0,\dots,|L(\sigma)|\}$, $r\in\{0,\dots,|R(\sigma)|\}$; the seed weight $w(\sigma)$ is the uniform product weight on these ingredients. Write $B(\sigma)=\{i\}\cup R(\sigma)$ for Bob's reverse side, and for $s\subseteq M$ put $\nu(s)=\dfrac{2\,|s|}{2^{|M|}\,|M|}$. The theorem states that for every **nonempty** $s$, $$\sum_{\sigma}\mathbf{1}\!\left[B(\sigma)=s\right]\frac{w(\sigma)}{\nu(s)}=1 ,$$ i.e. the seed mass of the fibre $\{\sigma:B(\sigma)=s\}$ is precisely $\nu(s)$, so the rescaled restriction of the seed law to that fibre is a probability distribution on seeds. It is the mirror image, with the roles of the two colour classes exchanged, of the corresponding statement for Alice's side.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L31674-L31702

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_20
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Basic
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseBobConditionalSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (nonempty : side.Nonempty) :
    (∑ seed : ExactForwardSeed M,
      exactReverseBobConditionalSeedWeight side seed) = 1 := by sorry
