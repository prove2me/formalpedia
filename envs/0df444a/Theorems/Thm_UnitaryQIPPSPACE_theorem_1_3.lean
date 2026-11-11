-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_theorem_1_3
-- name    : UnitaryQIPPSPACE.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:57.391395+00:00
-- url     : https://prove2.me/theorems/e9c09b55-6949-49d0-b80e-7e4150a24cff
-- title:
--   Theorem 1.3 — $\mathsf{unitaryQIP}=\mathsf{unitaryPSPACE}$
-- statement:
--   The unitary families synthesizable by a polynomial-time quantum verifier interacting with an untrusted prover are exactly the unitary families synthesizable in polynomial space:
--   $$\mathsf{unitaryQIP}=\mathsf{unitaryPSPACE},$$
--   where $\mathsf{unitaryQIP}=\bigcap_{p}\mathsf{unitaryQIP}_{0,\frac12,\frac1p}$ and $\mathsf{unitaryPSPACE}=\bigcap_p\mathsf{unitaryPSPACE}_{\frac1p}$, both intersections over all polynomials.
--
--   This is the unitary analogue of $\mathsf{QIP}=\mathsf{PSPACE}$ and $\mathsf{stateQIP}=\mathsf{statePSPACE}$.
--
--   Differences from the source:
--   - encoding: intersections over all polynomials p, error 1/p → intersections over all p ∈ ℕ[X], error 1/(p(n)+1); reason: both classes are monotone in the error and the two families of inverse polynomials are mutually cofinal, so the intersections are equal
--   - encoding: the gate set G is fixed "without loss of generality, … for example, {H, T, CNOT}" → G = {H, T, CNOT} exactly; reason: the paper's own example; the classes do not depend on the choice of a finite universal gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
--   - reading: space-uniform: a polynomial-space machine "on input (1^n, i), outputs the i-th operation of C_n" → for every i ≤ |C_n| the machine on (1^n, bin i) uses at most p(n) cells and outputs the i-th operation, or the empty string at i = |C_n|; reason: the end marker makes the machine determine the circuit (the standard reading of [MY23]); it bounds |C_n| by 2^{O(p(n))}
--   - encoding: a prover is a unitary on (M, Y) with an arbitrarily large private register Y → any number y of private qubits and any unitary on M ⊗ Y, private register starting in |0⋯0⟩; reason: the paper's model, with y chosen by the prover
--   - encoding: unitaryQIP_{c,s,δ} assumes 1 − c(n) > s(n) for all n → the set is empty when the condition fails; reason: the paper's class is undefined then; every use satisfies the condition
--   - encoding: the conditioned output is undefined at acceptance probability 0 → the zero matrix; reason: it is only used when the acceptance probability exceeds s ≥ 0
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Theorem 1.3, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_unitaryQIP
import Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACE

namespace UnitaryQIPPSPACE

/-- **Theorem 1.3** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version
sha256 9e357a00…, p. 3 (PDF p. 5)): "`unitaryQIP = unitaryPSPACE`."

Both sides are the subscript-free classes of p. 3: `unitaryQIP = ⋂_p unitaryQIP_{0,1/2,1/p}` and
`unitaryPSPACE = ⋂_p unitaryPSPACE_{1/p}` over all polynomials `p`.

**Formalization Note** Polynomials have natural-number coefficients and the error is
`1/(p(n) + 1)`, which gives the same intersections as all real polynomials `p ≥ 1`. Circuits use
the gate set `{H, T, CNOT}` with initialization, partial trace and measurement; uniformity is by
the published deterministic Turing machines `QAdvFew.PoQOracle.OTM`. -/
theorem theorem_1_3 : unitaryQIP = unitaryPSPACE := by sorry

end UnitaryQIPPSPACE
