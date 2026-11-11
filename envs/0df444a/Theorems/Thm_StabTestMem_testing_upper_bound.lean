-- Prove2me | Theorems.Thm_StabTestMem_testing_upper_bound
-- name    : StabTestMem.testing_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:02.934034+00:00
-- url     : https://prove2.me/theorems/4e86eb31-1fa6-4ba7-a39f-b9f50561e5ef
-- title:
--   Theorem 4.1 — adaptive tester with $k$ memory qubits (corrected: (n−k+1)/ε copies, k ≥ n allowed)
-- statement:
--   There is an absolute constant $C$ such that for all $n,k\ge0$ and every $\varepsilon>0$ there is an adaptive protocol that uses exactly $k$ qubits of quantum memory and
--
--   $$t\le C\,\frac{(n-k)^{+}+1}{\varepsilon}$$
--
--   single copies of an unknown $n$-qubit pure state $|\psi\rangle$, accepts with probability at least $2/3$ whenever $\mathcal F_{\mathsf{Stab}}(|\psi\rangle)=1$, and accepts with probability at most $1/3$ whenever $\mathcal F_{\mathsf{Stab}}(|\psi\rangle)\le1-\varepsilon$. Here $(n-k)^+=\max(n-k,0)$.
--
--   This is the upper half of Theorem 1.1: with $k$ qubits of memory, $O(n-k)$ copies suffice for constant $\varepsilon$.
--
--   Differences from the source:
--   - correction: O((n − k)/ε) copies, for k ≥ 0 → t ≤ C((n ∸ k) + 1)/ε for every k; reason: the printed bound is 0 at k = n and negative for k > n; for n = k = 1, ε = 0.2 both promises are inhabited (|0⟩, and the state with Bloch vector (1,1,1)/√3, F_Stab ≈ 0.789), while a 0-copy protocol accepts every input with the same probability; the paper's tester uses 4 + 2N = O(m + 1) copies per round (p. 35)
--   - reading: O(·) in the copy count → ∃ C uniform in n, k, ε (no threshold n₀); reason: the stronger of the two readings
--   - reading: distinguish → success probability ≥ 2/3 on every promised input (accept F_Stab = 1 w.p. ≥ 2/3, accept F_Stab ≤ 1 − ε w.p. ≤ 1/3); reason: the paper's notion (Lemma 5.1, p. 36; Lemma 5.3, p. 37)
--   - encoding: Definition 3.7: instruments in rounds 1, …, t−1 and a final POVM; adaptive single-copy protocol with a k-qubit memory → an instrument in every round (the last one's output memory discarded), a deterministic decision on the transcript, a finite outcome type; reason: a POVM {E^x} is the instrument Y ↦ Tr(E^x Y)η_*; randomness is absorbed into outcomes
--   - encoding: an unknown |ψ⟩ → testers are required to work on every unit vector ψ (copies |ψ⟩⟨ψ|); reason: the theorem is about pure inputs
--   - encoding: stabilizer state: a maximal Abelian subgroup of Paulis with P|ψ⟩ = ±|ψ⟩ → a unit vector fixed by a commuting subgroup of the Pauli group of order 2^n not containing −I; reason: the signs χ(u) are absorbed into the group elements ±P_u; same states
--   - encoding: F_Stab = max over Stab → sSup of the set of overlaps; reason: the set is nonempty, bounded and finite-valued, so the supremum is the maximum
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 4.1, p. 23

import Definitions.Def_StabTestMem_MemProtocol

namespace StabTestMem

open QAlgorithms

/-- **Theorem 4.1: the tester (corrected copy count `O((n − k + 1)/ε)`).** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 4.1, p. 23:
"Let k ≥ 0, ε > 0. There is an adaptive protocol that uses k qubits of memory and O((n−k)/ε) copies
of an unknown |ψ⟩ to distinguish between F_Stab(|ψ⟩) = 1 vs. F_Stab(|ψ⟩) ≤ 1−ε."

There is an absolute constant `C` such that for all `n, k` and every `ε > 0` some adaptive protocol
with exactly `k` qubits of memory and `t ≤ C((n ∸ k) + 1)/ε` single copies accepts every state with
`F_Stab = 1` with probability `≥ 2/3` and every state with `F_Stab ≤ 1 − ε` with probability `≤ 1/3`.

**Formalization Note.** Correction: the printed `O((n − k)/ε)` is `0` at `k = n` and negative for
`k > n`, while a `0`-copy protocol accepts every input with the same probability; for `n = k = 1`,
`ε = 0.2` both promises are inhabited (`|0⟩`; the state with Bloch vector `(1,1,1)/√3` has
`F_Stab ≈ 0.789`). The paper's tester uses `4 + 2N = O(m + 1)` copies per round (p. 35).
`n ∸ k` is truncated subtraction. The constant is uniform in `n, k, ε`. -/
theorem testing_upper_bound :
    ∃ C : ℝ, ∀ n k : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ (X : Type) (_ : Fintype X) (t : ℕ) (P : MemProtocol n k t X),
        (t : ℝ) ≤ C * (((n - k : ℕ) : ℝ) + 1) / ε ∧ P.IsStabTester ε := by sorry

end StabTestMem
