-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_theorem_1_2
-- name    : UnitaryQIPPSPACE.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:04.941009+00:00
-- url     : https://prove2.me/theorems/1d2f993c-9f3c-41ba-b6f6-c498108c6b1b
-- title:
--   Theorem 1.2 — $\mathsf{unitaryPSPACE}_{\delta^2/2^{14}}\subseteq\mathsf{unitaryQIP}_{0,s,\delta}$
-- statement:
--   Let $\delta,s:\mathbb N\to[0,1]$ satisfy $1/q(n)\le s(n)<1$ and $\delta(n)\ge1/r(n)$ for some polynomials $q,r$ with $q(n)\ge2$ and $r(n)\ge4$. Then
--   $$\mathsf{unitaryPSPACE}_{\delta^2/2^{14}}\subseteq\mathsf{unitaryQIP}_{0,s,\delta}.$$
--
--   This is the inclusion $\mathsf{unitaryPSPACE}\subseteq\mathsf{unitaryQIP}$ with perfect completeness and any inverse-polynomial soundness threshold.
--
--   Differences from the source:
--   - encoding: polynomials q, r → q, r ∈ ℕ[X]; reason: a real polynomial with q ≥ 2 (r ≥ 4) is dominated by one with natural coefficients and the hypotheses are monotone in q, r, so the hypothesis sets coincide
--   - encoding: the gate set G is fixed "without loss of generality, … for example, {H, T, CNOT}" → G = {H, T, CNOT} exactly; reason: the paper's own example; the classes do not depend on the choice of a finite universal gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
--   - reading: space-uniform: a polynomial-space machine "on input (1^n, i), outputs the i-th operation of C_n" → for every i ≤ |C_n| the machine on (1^n, bin i) uses at most p(n) cells and outputs the i-th operation, or the empty string at i = |C_n|; reason: the end marker makes the machine determine the circuit (the standard reading of [MY23]); it bounds |C_n| by 2^{O(p(n))}
--   - encoding: a prover is a unitary on (M, Y) with an arbitrarily large private register Y → any number y of private qubits and any unitary on M ⊗ Y, private register starting in |0⋯0⟩; reason: the paper's model, with y chosen by the prover
--   - encoding: unitaryQIP_{c,s,δ} assumes 1 − c(n) > s(n) for all n → the set is empty when the condition fails; reason: the paper's class is undefined then; every use satisfies the condition
--   - encoding: the conditioned output is undefined at acceptance probability 0 → the zero matrix; reason: it is only used when the acceptance probability exceeds s ≥ 0
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Theorem 1.2 (restated p.37), p.3 (PDF p.5)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_unitaryQIPc
import Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACEd

namespace UnitaryQIPPSPACE

/-- **Theorem 1.2** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version
sha256 9e357a00…, p. 3 (PDF p. 5), restated p. 37 (PDF p. 39)): "Let `δ, s : ℕ → [0, 1]` satisfy
`1/q(n) ≤ s(n) < 1` and `δ(n) ≥ 1/r(n)` for some polynomials `q, r` with `q(n) ≥ 2` and `r(n) ≥ 4`.
Then, it holds that `unitaryPSPACE_{δ²/2¹⁴} ⊆ unitaryQIP_{0,s,δ}`."

**Formalization Note** `q, r` are polynomials with natural-number coefficients; every real
polynomial with `q ≥ 2`, `r ≥ 4` is dominated by such a polynomial, and the hypotheses are
monotone in `q, r`, so the hypothesis sets coincide. -/
theorem theorem_1_2 (δ s : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n ∧ δ n ≤ 1) (hs : ∀ n, 0 ≤ s n ∧ s n ≤ 1)
    (hqr : ∃ q r : Polynomial ℕ, ∀ n, 2 ≤ q.eval n ∧ 4 ≤ r.eval n ∧
      1 / ((q.eval n : ℕ) : ℝ) ≤ s n ∧ s n < 1 ∧ 1 / ((r.eval n : ℕ) : ℝ) ≤ δ n) :
    unitaryPSPACEd (fun n => δ n ^ 2 / 2 ^ 14) ⊆ unitaryQIPc (fun _ => 0) s δ := by sorry

end UnitaryQIPPSPACE
