-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_65
-- name    : SingleInteraction.Supplement.theorem_65
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:10:53.625247+00:00
-- url     : https://prove2.me/theorems/82e004ad-b647-4765-994a-b28383143f99
-- title:
--   Theorem 65 — a fixed 8-local interaction for which geometrically local SIH$_8$ on $\mathbb Z^2$ is QMA-complete
-- statement:
--   There are a fixed 8-qubit Hermitian interaction $h$ with polynomial-time computable entries and constants $\Delta,R$ such that SIH$_8$ with interaction $h$ is QMA-complete even when restricted to instances whose qubits are placed injectively in the lattice $\mathbb Z^2$ with every qubit in at most $\Delta$ interaction tuples (bounded vertex degree) and any two qubits of a tuple at lattice distance at most $R$ (bounded interaction range).
--
--   Geometric locality and a single unweighted interaction are thus compatible with QMA-hardness.
--
--   Differences from the source:
--   - encoding: X-complete, with poly(n) bit lengths and an inverse-polynomial gap → membership for every exponent c and X-hardness for some c of the problem at exponent c; reason: the published theorem_60 convention; hardness at c implies hardness at every c′ ≥ c because the valid sets grow
--   - reading: QMA (Definition 2, p.16; an adapted, equivalent form by Remark 1) → the published InQMA / QMAHard: uniform polynomial-size {H, T, CNOT} verifiers, completeness 2/3, soundness 1/3, polynomial-time many-one reductions; reason: the base mission’s declared reading of Definition 2 (Remark 1 calls it equivalent to the standard class)
--   - reading: restricted to interaction hypergraphs that admit an injective embedding in a two-dimensional lattice with bounded degree and range (Definition 19, D = 2) → instances carrying an injective placement of the qubits in ℤ², with ∃ Δ R (before the exponent) bounding the degree and the ℓ¹ range; reason: the embedding is part of the instance, as the paper’s reductions output it; dropping it maps the problem to the existence reading, and any fixed norm gives the same notion since R is existential
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 65, p.71

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Variants

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 65 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held
version, sha256 19ddc444…), §5.4, p.71): "There exists a fixed 8-local Hermitian interaction `h` for
which `SIH8` is QMA-complete even when restricted to interaction hypergraphs embedded in a
two-dimensional lattice with bounded vertex degree and bounded interaction range."

There are an 8-qubit Hermitian `h` with polynomial-time computable entries and constants `Δ, R` such
that `SIH_8` with interaction `h`, restricted to instances given with an injective embedding of the
qubits into `ℤ²` in which every qubit lies in at most `Δ` tuples and any two qubits of a tuple are at
lattice distance at most `R`, is in QMA for every exponent `c` and QMA-hard for some `c`.

**Formalization Note** The geometric restriction is `geoSihProblem` (Definition 19 with `D = 2`; the
embedding is part of the instance, `ℓ¹` distance). "Bounded" means constants independent of the
instance (Definition 19), so `Δ, R` are chosen after `h` and before `c`. QMA notions as in the
published `theorem_60`. -/
theorem theorem_65 :
    ∃ h : Matrix (Fin 8 → Fin 2) (Fin 8 → Fin 2) ℂ, h.IsHermitian ∧ EntriesPolyTime h ∧
      ∃ Δ R : ℕ, (∀ c : ℕ, InQMA (onCodes geoCodec (geoSihProblem 8 h Δ R c))) ∧
        ∃ c : ℕ, QMAHard geoCodec.encode (geoSihProblem 8 h Δ R c) := by sorry

end Supplement

end SingleInteraction
