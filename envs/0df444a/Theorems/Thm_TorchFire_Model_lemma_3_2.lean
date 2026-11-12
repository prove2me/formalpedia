-- Prove2me | Theorems.Thm_TorchFire_Model_lemma_3_2
-- name    : TorchFire.Model.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:35:58.690196+00:00
-- url     : https://prove2.me/theorems/900c093a-b6ed-4c59-8e8f-4cd3956c4c37
-- title:
--   Lemma 3.2 (BBBV hybrid bound) — $D(\sigma^1,\sigma^0)\le2\sqrt{qM}$
-- statement:
--   Consider two executions $b\in\{0,1\}$ of a quantum algorithm with the same initial state $\rho$ and the same unitary operations $G_0,\dots,G_q$ between queries; at query $j\in[q]$ execution $b$ applies a query unitary $O^b_j$. For each $j$ let $P_j$ be a projector with
--   $$(O^1_j-O^0_j)(I-P_j)=0,$$
--   i.e. on every input outside the support of $P_j$ both oracles act identically. Let $\rho_j$ be the state immediately before query $j$ in execution $1$, $\sigma^b$ the final state of execution $b$, and $M=\sum_{j=1}^q\mathrm{Tr}(P_j\rho_j)$. Then
--   $$D(\sigma^1,\sigma^0)=\tfrac12\Vert\sigma^1-\sigma^0\Vert_1\le2\sqrt{qM}.$$
--
--   This is the hybrid bound of [BBBV97] in the form used by Lemma 8.3. It is more general than the Open platform item `ClonableQMASep.Main.lemma_1` (function oracles agreeing off a basis set, pure start).
--
--   Differences from the source:
--   - generalization: P_j a projector on the query registers, ρ_j the state of the query input register → P_j any projector on the whole space, ρ_j the global state before query j; reason: P ⊗ I is such a projector and Tr((P ⊗ I)ρ) = Tr(P ρ_query)
--   - encoding: a mixed initial state → a density operator (WildeQIT.IsDensityOperator); reason: the same set
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 3.2, p.18 ([BBBV97])

import Mathlib
import Definitions.Def_TorchFire_Model_OracleAlg
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix

namespace TorchFire.Model

/-- **Lemma 3.2** (BBBV hybrid bound [BBBV97]), p.18 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). Consider two executions `b ∈ {0, 1}` of a
`q`-query computation with the same initial state `ρ` and the same unitaries `G_0, …, G_q` between
queries; at query `j` execution `b` applies the query unitary `O^b_j`. Let `P_j` be projectors with
`(O^1_j − O^0_j)(I − P_j) = 0`. Let `ρ_j` be the state immediately before query `j` in execution `1`,
`σ^b` the final state of execution `b`, and `M = Σ_{j=1}^q Tr(P_j ρ_j)`. Then
`D(σ^1, σ^0) = ½‖σ^1 − σ^0‖_1 ≤ 2√(qM)`.

This generalizes the Open item `ClonableQMASep.Main.lemma_1` (function oracles agreeing off a basis
set, pure start) to a mixed start, arbitrary query unitaries and arbitrary projectors. -/
theorem lemma_3_2 {S : Type} [Fintype S] [DecidableEq S] (q : ℕ) (G O1 O0 P : ℕ → Matrix S S ℂ)
    (ρ : Matrix S S ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (hG : ∀ j ≤ q, G j ∈ Matrix.unitaryGroup S ℂ)
    (hO : ∀ j < q, O1 j ∈ Matrix.unitaryGroup S ℂ ∧ O0 j ∈ Matrix.unitaryGroup S ℂ)
    (hP : ∀ j < q, (P j).IsHermitian ∧ P j * P j = P j)
    (hwit : ∀ j < q, (O1 j - O0 j) * (1 - P j) = 0) :
    traceDist (conjMat (evolve G O1 q) ρ) (conjMat (evolve G O0 q) ρ) ≤
      2 * Real.sqrt ((q : ℝ) *
        ∑ j ∈ Finset.range q, (Matrix.trace (P j * conjMat (evolve G O1 j) ρ)).re) := by sorry

end TorchFire.Model
