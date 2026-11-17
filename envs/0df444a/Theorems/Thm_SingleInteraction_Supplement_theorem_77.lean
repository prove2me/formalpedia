-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_77
-- name    : SingleInteraction.Supplement.theorem_77
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:15:00.58712+00:00
-- url     : https://prove2.me/theorems/805fc2c6-696f-41e7-853c-9c3112f6ba1a
-- title:
--   Theorem 77 — a uniform family of 9-local stoquastic interactions for which geometrically local Stoq-DSIH$_9$ on $\mathbb Z^2$ is StoqMA-complete
-- statement:
--   There are a family $\{h^{(n)}\}_{n\ge1}$ of 9-qubit Hermitian matrices, each stoquastic in the computational basis and uniform in the sense of Definition 32, and constants $\Delta,R$ such that Stoq-DSIH$_9$ with this family is StoqMA-complete even when restricted to instances whose qubits are placed injectively in $\mathbb Z^2$ with every qubit in at most $\Delta$ tuples and any two qubits of a tuple at lattice distance at most $R$.
--
--   Stoquasticity, geometric locality and a single size-dependent interaction combine without loss of StoqMA-hardness.
--
--   Differences from the source:
--   - encoding: StoqMA-complete → membership in StoqMA for every exponent c and StoqMA-hardness for some c; reason: the published theorem_60 convention
--   - reading: StoqMA thresholds ϵyes, ϵno with inverse-polynomial gap (Definition 5) → thresholds computable to precision 2^{−q} in polynomial time, gap ≥ 1/(|x|+1)^d; reason: Definition 5 leaves their computability implicit; the class of [BBT06] and every reduction of the paper compute them
--   - reading: restricted to interaction hypergraphs that admit an injective embedding in a two-dimensional lattice with bounded degree and range (Definition 19, D = 2) → instances carrying an injective placement of the qubits in ℤ², with ∃ Δ R (before the exponent) bounding the degree and the ℓ¹ range; reason: the embedding is part of the instance, as the paper’s reductions output it; dropping it maps the problem to the existence reading, and any fixed norm gives the same notion since R is existential
--   - reading: a finite gate set universal for classical reversible computation, output qubit measured in the Hadamard basis (Definition 5) → the gates X, CNOT, Toffoli, output qubit 0 measured in the Hadamard basis, accepting on +; reason: the gate set of [BBT06]; any two finite classical-reversible universal gate sets simulate each other with polynomial overhead given the |0⟩, |1⟩ ancillas of Definition 5
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 77, p.88

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_UniformFamily
import Definitions.Def_SingleInteraction_Supplement_Linalg
import Definitions.Def_SingleInteraction_Supplement_StoqMA
import Definitions.Def_SingleInteraction_Supplement_Variants

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 77 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held
version, sha256 19ddc444…), §8, p.88): "There exists a uniform family of 9-local stoquastic Hermitian
interactions `{h(n)}n≥1` for which geometrically local Stoq-DSIH9 is StoqMA-complete even when
restricted to two-dimensional lattice embeddings."

There are a family `{h^(n)}_{n≥1}` of 9-qubit Hermitian matrices, each stoquastic in the computational
basis and uniform in the sense of Definition 32, and constants `Δ, R` such that `DSIH_9` with this family,
restricted to instances given with an injective embedding of the qubits into `ℤ²` in which every qubit
lies in at most `Δ` tuples and any two qubits of a tuple are at lattice distance at most `R`, is in
StoqMA for every exponent `c` and StoqMA-hard for some `c`.

**Formalization Note** The restriction is `geoDsihProblem` (Definition 19 with `D = 2`; the embedding is
part of the instance; `ℓ¹` distance; `Δ, R` fixed before the instance). Stoq-`DSIH` (Definition 34)
restricts only the family, asserted by `IsStoquastic (h^(n))`. StoqMA follows Definition 5
(`InStoqMA`). Membership for every `c`, hardness for some `c`. -/
theorem theorem_77 :
    ∃ hfam : ℕ → Matrix (Fin 9 → Fin 2) (Fin 9 → Fin 2) ℂ,
      (∀ n : ℕ, 1 ≤ n → (hfam n).IsHermitian ∧ IsStoquastic (hfam n)) ∧ UniformFamily hfam ∧
        ∃ Δ R : ℕ, (∀ c : ℕ, InStoqMA (onCodes geoCodec (geoDsihProblem 9 hfam Δ R c))) ∧
          ∃ c : ℕ, StoqMAHard geoCodec.encode (geoDsihProblem 9 hfam Δ R c) := by sorry

end Supplement

end SingleInteraction
