-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P01_nonBasisPreserving_oneQubit_universal
-- name    : QAlgorithms.Papers.Independent.Renew46.P01.nonBasisPreserving_oneQubit_universal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:42:55.073987+00:00
-- url     : https://prove2.me/theorems/980dd049-a1c6-45f7-96af-ff722357cc98
-- title:
--   Every non-basis-preserving one-qubit unitary gives universality with B
-- statement:
--   Let $B$ contain every basis-preserving unitary gate on every finite number of qubits: each computational basis vector is mapped to another computational basis vector times a complex phase. Let $g$ be a unitary acting on exactly one qubit, and suppose $g$ is not basis preserving. Then
--
--   $$
--   B\cup\{g\}\text{ is universal}.
--   $$
--
--   Explicitly, for every number $k$ of target qubits, every $k$-qubit unitary $V$, and every $\delta>0$, a finite circuit $C$ over this set exists on those $k$ wires such that $\|V-e^{i\theta}C\|_{\mathrm{op}}\le\delta$ for some real $\theta$.
--
--   This is an unconditional group-generation statement. Universality allows a global phase and requires no ancillary wires; it makes no claim about polynomial circuit length.
-- source:
--   Generalised Coupling and An Elementary Algorithm for the Quantum Schur Transform, arXiv:2305.04069v3, PDF p. 23, Theorem VI.1: a non-basis-preserving one-qubit gate gives universality

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P01

open scoped BigOperators ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF pp.23--24, Theorem VI.1: adjoining any single-qubit unitary
outside B to all basis-preserving gates gives a universal set. The frozen
IsUniversal means approximation up to global phase on the target's own
wires, with no ancillas. No complexity-theoretic assumption is imposed. -/
theorem nonBasisPreserving_oneQubit_universal
    (g : Gate) (hg : g.IsUnitary) (hArity : g.arity = 1)
    (hNonBasis : ¬ BasisPreserving g) :
    IsUniversal (basisPreservingGates ∪ {g}) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P01

end
