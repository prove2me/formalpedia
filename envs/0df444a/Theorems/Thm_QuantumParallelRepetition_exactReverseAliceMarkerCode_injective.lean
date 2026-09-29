-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceMarkerCode_injective
-- name    : QuantumParallelRepetition.exactReverseAliceMarkerCode_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T03:32:04.933785+00:00
-- url     : https://prove2.me/theorems/ddbe7f39-4ff1-4ab6-b129-6e052d46867d
-- title:
--   A seed is determined by Alice's side, its context and the marker position
-- statement:
--   Recall that a *seed* over a finite type $M$ is a tuple $\sigma=(i,\pi,\tau_L,\tau_R,\ell,r)$ consisting of a marked coordinate $i\in M$, a two-colouring $\pi:M\to\{0,1\}$, orderings $\tau_L,\tau_R$ of the two colour classes $L(\sigma)=\{j\neq i:\pi(j)=0\}$ and $R(\sigma)=\{j\neq i:\pi(j)=1\}$, and cut positions $\ell\in\{0,\dots,|L(\sigma)|\}$, $r\in\{0,\dots,|R(\sigma)|\}$; the seed weight $w(\sigma)$ is the uniform product weight on these ingredients. Encode a seed by the triple consisting of Alice's side $A(\sigma)=\{i\}\cup L(\sigma)$; the *side context*, which records the complementary set $M\setminus A(\sigma)=R(\sigma)$, the enumeration of $A(\sigma)$ obtained from $\tau_L$ by inserting the marked coordinate at position $\ell$, the enumeration of $R(\sigma)$ obtained from $\tau_R$, the cut $r$, and the bit $\pi(i)$; and the *marker*, the position of $i$ in the enumeration of $A(\sigma)$. The theorem asserts that this encoding is injective: two seeds with the same side, context and marker are equal.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L32716-L32864

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_21
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseAliceMarkerCode_injective
    {M : Type*} [Fintype M] [DecidableEq M] :
    Function.Injective (exactReverseAliceMarkerCode (M := M)) := by sorry
