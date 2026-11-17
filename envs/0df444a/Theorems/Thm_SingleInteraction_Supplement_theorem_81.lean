-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_81
-- name    : SingleInteraction.Supplement.theorem_81
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:16:39.993512+00:00
-- url     : https://prove2.me/theorems/2d839f2e-e484-43e4-85ad-4c9292c64d3b
-- title:
--   Theorem 81 — for the interaction $h$ of eq. (45), geometrically local Precise-SIH$_8$ is PSPACE-complete
-- statement:
--   Let $h$ be the 8-qubit interaction of eq. (45), the interaction of Theorem 65. Then $h$ is Hermitian with polynomial-time computable entries, and for some constants $\Delta,R$ the problem Precise-SIH$_8$ with interaction $h$ (promise gap $b-a\ge2^{-p(n)}$), restricted to instances whose qubits are placed injectively in $\mathbb Z^2$ with every qubit in at most $\Delta$ tuples and any two qubits of a tuple at lattice distance at most $R$, is PSPACE-complete.
--
--   With exponentially small promise gaps the same geometrically local interaction captures polynomial space.
--
--   Differences from the source:
--   - encoding: PSPACE-complete, b − a ≥ 2^{−p(n)} → membership in PSPACE for every exponent c and PSPACE-hardness for some c, gap ≥ 2^{−(n+1)^c}; reason: the published theorem_60 convention
--   - reading: the same fixed 8-local interaction h as in Theorem 65 → the explicit h of eq. (45), shown Hermitian with polynomial-time entries; reason: eq. (45) is the interaction constructed for Theorem 65 (§5.4.3)
--   - reading: restricted to interaction hypergraphs that admit an injective embedding in a two-dimensional lattice with bounded degree and range (Definition 19, D = 2) → instances carrying an injective placement of the qubits in ℤ², with ∃ Δ R (before the exponent) bounding the degree and the ℓ¹ range; reason: the embedding is part of the instance, as the paper’s reductions output it; dropping it maps the problem to the existence reading, and any fixed norm gives the same notion since R is existential
--   - encoding: PSPACE (eq. (1)) for promise problems → InPromisePSPACE: some language decided by the published polynomial-space multi-stack machine model (OptimalQueuingComplexity.Restless.InPSPACE) contains every YES and no NO input; PSPACE-hardness by PolynomialManyOne reductions; reason: the standard class for promise problems on the bit-string layer of InQMA
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 81, p.98

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Classes
import Definitions.Def_SingleInteraction_Supplement_Interactions
import Definitions.Def_SingleInteraction_Supplement_Variants

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 81 (Precise geometrically local single-interaction Hamiltonians) (Hecker, *The Complexity of
Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §9.3, p.98): "For
the same fixed 8-local interaction `h` as in Theorem 65, the geometrically local Precise-SIH8 problem is
PSPACE-complete."

For the 8-qubit interaction `h` of eq. (45) (Barenco, SWAP and identity propagation branches with the
factor `1/4`, plus `I ⊗ h_check(v7, v8)`): `h` is Hermitian with polynomial-time computable entries, and
for some constants `Δ, R` the problem Precise-`SIH_8` with interaction `h` (Definition 40: promise gap
`b − a ≥ 2^{−p(n)}`), restricted to instances given with an injective embedding of the qubits into `ℤ²`
with every qubit in at most `Δ` tuples and any two qubits of a tuple at lattice distance at most `R`, is
in PSPACE for every exponent `c` and PSPACE-hard for some `c`.

**Formalization Note** `h` is `h45`. The restriction is `geoPreciseSihProblem` (gap `≥ 2^{−(n+1)^c}`,
threshold codes of at most `(n+1)^c` bits). PSPACE for promise problems and PSPACE-hardness under
`PolynomialManyOne` are those of `Def_SingleInteraction_Supplement_Classes`. Membership for every `c`,
hardness for some `c`. -/
theorem theorem_81 :
    h45.IsHermitian ∧ EntriesPolyTime h45 ∧
      ∃ Δ R : ℕ, (∀ c : ℕ, InPromisePSPACE (onCodes geoCodec (geoPreciseSihProblem 8 h45 Δ R c))) ∧
        ∃ c : ℕ, PSPACEHard geoCodec.encode (geoPreciseSihProblem 8 h45 Δ R c) := by sorry

end Supplement

end SingleInteraction
