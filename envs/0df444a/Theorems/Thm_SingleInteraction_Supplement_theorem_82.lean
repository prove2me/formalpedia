-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_82
-- name    : SingleInteraction.Supplement.theorem_82
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:17:19.333943+00:00
-- url     : https://prove2.me/theorems/b048b2e2-9dad-44a8-ac7b-a130496503ad
-- title:
--   Theorem 82 — a fixed 9-local interaction for which Guided-SIH$_9$ is BQP-complete, hardness also with a unique, gapped ground state and overlap $1-1/\mathrm{poly}(n)$
-- statement:
--   There is a fixed 9-qubit Hermitian interaction $h_G$ with polynomial-time computable entries such that
--
--   1. Guided-SIH$_9$ with interaction $h_G$ is BQP-complete;
--   2. BQP-hardness holds even for instances whose Hamiltonian has a unique ground state, separated from the rest of the spectrum by an inverse-polynomial gap, and whose semi-classical subset guiding state $|u\rangle$ has overlap $1-1/\mathrm{poly}(n)$ with the ground state.
--
--   Guiding states make the single-interaction ground-energy problem exactly as hard as quantum computation.
--
--   Differences from the source:
--   - encoding: BQP-complete → membership in BQP for every exponent c and BQP-hardness for some c; reason: the published theorem_60 convention
--   - encoding: unique ground state, inverse-polynomial gap, overlap 1 − 1/poly(n) → ∃ exponents p_gap, q (and c), chosen before the instance: one-dimensional ground space, specGap ≥ 1/(n+1)^{p_gap}, a unit ground state ϕ with |⟨u|ϕ⟩| ≥ 1 − 1/(n+1)^q; reason: the polynomials of the statement are existential and fixed before the instance
--   - reading: BQP (Definition 1): polynomial-size uniform quantum circuits, 2/3 and 1/3 → the published QuantumVerifier with zero witness qubits: uniform polynomial-size {H, T, CNOT} circuits, acceptance ≥ 2/3 on YES and ≤ 1/3 on NO; BQP-hardness by PolynomialManyOne reductions; reason: the base mission’s gate set and verifier layer; {H, T, CNOT} is universal, so the class is the same
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 82, p.100

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Classes
import Definitions.Def_SingleInteraction_Supplement_Variants

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 82 (Guided single-interaction Hamiltonians) (Hecker, *The Complexity of Single-Interaction
Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §9.4, p.100): "There exists a fixed
9-local Hermitian interaction `hG` such that Guided-SIH9 is BQP-complete. Moreover, BQP-hardness holds
even for instances with a unique ground state separated from the remainder of the spectrum by an
inverse-polynomial gap and with a semi-classical subset guiding state having overlap `1 − 1/poly(n)`
with the ground state."

There is a 9-qubit Hermitian interaction `h_G` with polynomial-time computable entries such that
1. Guided-`SIH_9` with `h_G` (Definition 41) is in BQP for every exponent `c` and BQP-hard for some `c`;
2. for some exponents `p_gap, q` (polynomials `(n+1)^{p_gap}`, `(n+1)^q`) and some `c`, Guided-`SIH_9`
   restricted to instances whose Hamiltonian has a one-dimensional ground space, spectral gap at least
   `1/(n+1)^{p_gap}` above it, and a normalized ground state `ϕ` with `|⟨u|ϕ⟩| ≥ 1 − 1/(n+1)^q` for the
   semi-classical guiding state `|u⟩` is BQP-hard.

**Formalization Note** Guided-`SIH` is `guidedSihProblem`; the restriction of item 2 is
`guidedSihProblemOn … (GuidedInstance.WellGuided 9 h_G p_gap q)`. BQP (Definition 1) and BQP-hardness
are those of `Def_SingleInteraction_Supplement_Classes`. Membership for every `c`, hardness for some `c`;
the polynomials of item 2 are chosen before the instance. -/
theorem theorem_82 :
    ∃ h : Matrix (Fin 9 → Fin 2) (Fin 9 → Fin 2) ℂ, h.IsHermitian ∧ EntriesPolyTime h ∧
      (∀ c : ℕ, InBQP (onCodes guidedCodec (guidedSihProblem 9 h c))) ∧
        (∃ c : ℕ, BQPHard guidedCodec.encode (guidedSihProblem 9 h c)) ∧
          ∃ pg q c : ℕ, BQPHard guidedCodec.encode
            (guidedSihProblemOn 9 h c (GuidedInstance.WellGuided 9 h pg q)) := by sorry

end Supplement

end SingleInteraction
