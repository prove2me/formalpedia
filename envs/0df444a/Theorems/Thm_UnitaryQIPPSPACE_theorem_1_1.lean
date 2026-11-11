-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_theorem_1_1
-- name    : UnitaryQIPPSPACE.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:57.141579+00:00
-- url     : https://prove2.me/theorems/4802c5be-7de3-433f-8b65-1630e7483daf
-- title:
--   Theorem 1.1 — $\mathsf{unitaryQIP}_{c,s,\delta}\subseteq\mathsf{unitaryPSPACE}_{c+\varepsilon+7\delta}$
-- statement:
--   Let $c,s,\varepsilon,\delta:\mathbb N\to[0,1]$ be such that $\varepsilon(n)\ge1/(q(n)+1)$ for some polynomial $q$, and for all $n$
--   $$\varepsilon(n)\le\frac{1-c(n)-s(n)}4,\qquad\delta(n)\le\frac{(1-c(n)-s(n))^2}8.$$
--   Then
--   $$\mathsf{unitaryQIP}_{c,s,\delta}\subseteq\mathsf{unitaryPSPACE}_{c+\varepsilon+7\delta}.$$
--
--   This is the inclusion $\mathsf{unitaryQIP}\subseteq\mathsf{unitaryPSPACE}$ with explicit errors.
--
--   Differences from the source:
--   - generalization: ε(n) = 1/q(n) for some polynomial q → ε(n) ≥ 1/(q(n)+1) for some q ∈ ℕ[X]; reason: every ε = 1/q (q a real polynomial, q ≥ 1 since ε ≤ 1) satisfies it; it follows from the printed theorem applied to 1/(q+1) ≤ ε and monotonicity of unitaryPSPACE in its error
--   - encoding: unitaryPSPACE_δ for δ : ℕ → [0,1] → unitaryPSPACE_δ for every real δ; reason: the index c + ε + 7δ may exceed 1; the definition is the same formula
--   - encoding: the gate set G is fixed "without loss of generality, … for example, {H, T, CNOT}" → G = {H, T, CNOT} exactly; reason: the paper's own example; the classes do not depend on the choice of a finite universal gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
--   - reading: space-uniform: a polynomial-space machine "on input (1^n, i), outputs the i-th operation of C_n" → for every i ≤ |C_n| the machine on (1^n, bin i) uses at most p(n) cells and outputs the i-th operation, or the empty string at i = |C_n|; reason: the end marker makes the machine determine the circuit (the standard reading of [MY23]); it bounds |C_n| by 2^{O(p(n))}
--   - encoding: a prover is a unitary on (M, Y) with an arbitrarily large private register Y → any number y of private qubits and any unitary on M ⊗ Y, private register starting in |0⋯0⟩; reason: the paper's model, with y chosen by the prover
--   - encoding: unitaryQIP_{c,s,δ} assumes 1 − c(n) > s(n) for all n → the set is empty when the condition fails; reason: the paper's class is undefined then; every use satisfies the condition
--   - encoding: the conditioned output is undefined at acceptance probability 0 → the zero matrix; reason: it is only used when the acceptance probability exceeds s ≥ 0
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Theorem 1.1 (restated p.13), p.3 (PDF p.5)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_unitaryQIPc
import Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACEd

namespace UnitaryQIPPSPACE

/-- **Theorem 1.1** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version
sha256 9e357a00…, p. 3 (PDF p. 5), restated p. 13 (PDF p. 15)): "Let `c, s, ε, δ : ℕ → [0, 1]` be such
that `ε(n) = 1/q(n)` for some polynomial `q(n)`, and `ε(n) ≤ (1 − c(n) − s(n))/4` and
`δ(n) ≤ (1 − c(n) − s(n))²/8` for all `n ∈ ℕ`. Then `unitaryQIP_{c,s,δ} ⊆ unitaryPSPACE_{c+ε+7δ}`."

**Formalization Note** "`ε(n) = 1/q(n)` for some polynomial `q`" is generalized to
"`ε(n) ≥ 1/(q(n) + 1)` for some polynomial `q` with natural-number coefficients", which every
`ε = 1/q` satisfies. -/
theorem theorem_1_1 (c s ε δ : ℕ → ℝ)
    (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (hs : ∀ n, 0 ≤ s n ∧ s n ≤ 1)
    (hε : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1) (hδ : ∀ n, 0 ≤ δ n ∧ δ n ≤ 1)
    (hq : ∃ q : Polynomial ℕ, ∀ n, 1 / (((q.eval n : ℕ) : ℝ) + 1) ≤ ε n)
    (hεb : ∀ n, ε n ≤ (1 - c n - s n) / 4) (hδb : ∀ n, δ n ≤ (1 - c n - s n) ^ 2 / 8) :
    unitaryQIPc c s δ ⊆ unitaryPSPACEd (fun n => c n + ε n + 7 * δ n) := by sorry

end UnitaryQIPPSPACE
