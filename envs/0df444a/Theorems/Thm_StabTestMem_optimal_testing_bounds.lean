-- Prove2me | Theorems.Thm_StabTestMem_optimal_testing_bounds
-- name    : StabTestMem.optimal_testing_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:11.342831+00:00
-- url     : https://prove2.me/theorems/e9de9ce0-df14-49a5-b8a1-e1eaef705cf7
-- title:
--   Theorem 1.1 — with $k$ qubits of memory, stabilizer testing takes $\Theta(n-k)$ copies (corrected: (n−k+1)/ε copies, k ≥ n allowed)
-- statement:
--   **Upper bound.** There is an absolute constant $C$ such that for all $n,k\ge0$ and every $\varepsilon>0$ some adaptive protocol with exactly $k$ qubits of quantum memory uses
--
--   $$t\le C\,\frac{(n-k)^{+}+1}{\varepsilon}$$
--
--   single copies of an unknown $n$-qubit pure state $|\psi\rangle$ and distinguishes $\mathcal F_{\mathsf{Stab}}(|\psi\rangle)=1$ from $\mathcal F_{\mathsf{Stab}}(|\psi\rangle)\le1-\varepsilon$: it accepts with probability $\ge2/3$ in the first case and $\le1/3$ in the second.
--
--   **Lower bound.** There are $c>0$ and $n_0$ such that for every $n\ge n_0$, every $k$, every $\varepsilon$ with $0<\varepsilon<1-n^2/2^n$, and every adaptive protocol with $k$ qubits of memory (any finite outcome alphabets) that is such a tester using $t$ copies,
--
--   $$t\ge c\,(n-k).$$
--
--   For constant $\varepsilon$ the copy complexity of stabilizer testing with $k$ qubits of memory is therefore $\Theta(n-k)$ (for $k\le n$).
--
--   Differences from the source:
--   - correction: O((n − k)/ε) copies, for k ≥ 0 → t ≤ C((n ∸ k) + 1)/ε for every k; reason: the printed bound is 0 at k = n and negative for k > n; for n = k = 1, ε = 0.2 both promises are inhabited (|0⟩, and the state with Bloch vector (1,1,1)/√3, F_Stab ≈ 0.789), while a 0-copy protocol accepts every input with the same probability; the paper's tester uses 4 + 2N = O(m + 1) copies per round (p. 35)
--   - reading: O(·) in the copy count → ∃ C uniform in n, k, ε (no threshold n₀); reason: the stronger of the two readings
--   - reading: every such tester needs Ω(n − k) copies → ∃ c > 0 ∃ n₀ ∀ n ≥ n₀ … t ≥ c(n − k); reason: Ω is asymptotic in n; with n₀ = 0 the statement is false: n = 1, k = 0, ε = 0.3 < 1 − 1/2, every one-qubit state has F_Stab ≥ 0.789 > 0.7, so 'always accept' with t = 0 is a tester
--   - reading: distinguish → success probability ≥ 2/3 on every promised input (accept F_Stab = 1 w.p. ≥ 2/3, accept F_Stab ≤ 1 − ε w.p. ≤ 1/3); reason: the paper's notion (Lemma 5.1, p. 36; Lemma 5.3, p. 37)
--   - encoding: Definition 3.7: instruments in rounds 1, …, t−1 and a final POVM; adaptive single-copy protocol with a k-qubit memory → an instrument in every round (the last one's output memory discarded), a deterministic decision on the transcript, a finite outcome type; reason: a POVM {E^x} is the instrument Y ↦ Tr(E^x Y)η_*; randomness is absorbed into outcomes
--   - encoding: an unknown |ψ⟩ → testers are required to work on every unit vector ψ (copies |ψ⟩⟨ψ|); reason: the theorem is about pure inputs
--   - encoding: stabilizer state: a maximal Abelian subgroup of Paulis with P|ψ⟩ = ±|ψ⟩ → a unit vector fixed by a commuting subgroup of the Pauli group of order 2^n not containing −I; reason: the signs χ(u) are absorbed into the group elements ±P_u; same states
--   - encoding: F_Stab = max over Stab → sSup of the set of overlaps; reason: the set is nonempty, bounded and finite-valued, so the supremum is the maximum
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 1.1, p. 4 (restated p. 36)

import Definitions.Def_StabTestMem_MemProtocol

namespace StabTestMem

open QAlgorithms

/-- **Theorem 1.1 (optimal testing bounds), both halves; corrected upper bound.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 1.1,
p. 4 (restated p. 36): "Let k ≥ 0, ε > 0. There is an adaptive protocol that uses k qubits of memory
and O((n−k)/ε) copies of an unknown |ψ⟩ to distinguish between F_Stab(|ψ⟩) = 1 vs.
F_Stab(|ψ⟩) ≤ 1 − ε. Also every such tester needs Ω(n − k) copies (for 0 < ε < 1 − n^2/2^n)."

(Upper) There is an absolute constant `C` such that for all `n, k` and every `ε > 0` some adaptive
protocol with exactly `k` qubits of memory using `t ≤ C((n ∸ k) + 1)/ε` copies is an `ε`-tester
(accepts `F_Stab = 1` with probability `≥ 2/3`, accepts `F_Stab ≤ 1 − ε` with probability `≤ 1/3`).
(Lower) There are `c > 0` and `n₀` such that for every `n ≥ n₀`, every `k`, every
`0 < ε < 1 − n²/2ⁿ`, every finite outcome alphabet and every adaptive protocol with `k` memory
qubits and `t` copies that is an `ε`-tester, `t ≥ c(n − k)`.

**Formalization Note.** Correction (upper): `O((n − k)/ε)` becomes `C((n ∸ k) + 1)/ε`, allowing every
`k`; the printed bound is `0` copies at `k = n` (for `n = k = 1`, `ε = 0.2` both promises are
inhabited, while a `0`-copy protocol accepts all inputs with the same probability) and negative for
`k > n`. Reading (lower): `Ω(n − k)` is asymptotic in `n` (`∃ n₀`); with `n₀ = 0` it is false
(`n = 1`, `k = 0`, `ε = 0.3`: every one-qubit state has `F_Stab ≥ 0.789 > 0.7`, so "always accept"
with `t = 0` is a tester). The upper constant is uniform in `n, k, ε`. For `k ≥ n` the lower
conjunct is trivially true, as in the paper. -/
theorem optimal_testing_bounds :
    (∃ C : ℝ, ∀ n k : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ (X : Type) (_ : Fintype X) (t : ℕ) (P : MemProtocol n k t X),
        (t : ℝ) ≤ C * (((n - k : ℕ) : ℝ) + 1) / ε ∧ P.IsStabTester ε) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k : ℕ, ∀ ε : ℝ, 0 < ε →
      ε < 1 - (n : ℝ) ^ 2 / 2 ^ n →
      ∀ (X : Type) [Fintype X] (t : ℕ) (P : MemProtocol n k t X),
        P.IsStabTester ε → c * ((n : ℝ) - k) ≤ t) := by sorry

end StabTestMem
