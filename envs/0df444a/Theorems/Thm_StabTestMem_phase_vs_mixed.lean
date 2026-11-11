-- Prove2me | Theorems.Thm_StabTestMem_phase_vs_mixed
-- name    : StabTestMem.phase_vs_mixed
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:36.498705+00:00
-- url     : https://prove2.me/theorems/94f1b4b8-ee9e-42dc-b86a-eb670065649c
-- title:
--   Theorem 5.9 — random degree-2 phase states versus the maximally mixed state
-- statement:
--   1. For every adaptive protocol with $k$ qubits of memory using $t<n$ single copies of an $n$-qubit state,
--
--   $$\mathbb E_{x\sim P_{\mathrm{mm}}}\big[|L(x)-1|\big]\le2^{2-(n-k-7t)/2}, \tag{106}$$
--
--   where $P_{\mathrm{mm}}(x)=\operatorname{Tr}[E_x]/2^{nt}$ and $L(x)=\operatorname{Tr}[E_x\sigma_P]/P_{\mathrm{mm}}(x)$.
--
--   2. Consequently $t=\Omega(n-k)$ copies are required to distinguish a uniformly random degree-2 phase state from the maximally mixed state: there is $c>0$ such that every such protocol (for any $n,k,t$) whose acceptance probabilities on $\rho_{\mathrm{mm}}$ and on a random degree-2 phase state differ by at least $1/3$ uses $t\ge c(n-k)$ copies.
--
--   Differences from the source:
--   - encoding: Definition 3.7: instruments in rounds 1, …, t−1 and a final POVM; adaptive single-copy protocol with a k-qubit memory → an instrument in every round (the last one's output memory discarded), a deterministic decision on the transcript, a finite outcome type; reason: a POVM {E^x} is the instrument Y ↦ Tr(E^x Y)η_*; randomness is absorbed into outcomes
--   - encoding: Tr[R(O)E_x], P_mm(x) = Tr[E_x]/2^{nt}, L(x) → the transcript functional P.weight evaluated at R(O), ρ_mm, σ (avgDev); reason: Lemma 3.10's E_x extended linearly to every t-copy operator
--   - generalization: t copies are required to distinguish (success ≥ 2/3 on each hypothesis) → any protocol whose acceptance probabilities on the two hypotheses differ by ≥ 1/3 has t ≥ …; reason: 2/3-correctness on each hypothesis gives an acceptance gap ≥ 1/3, so the Lean statement specializes to the paper's
--   - reading: t = Ω(n − k) → ∃ c > 0 with t ≥ c(n − k) for all n, k, t (no threshold n₀); reason: the stronger reading; a 0-copy protocol has acceptance gap 0, and for t ≥ 1 small n − k is absorbed by c
--   - encoding: a random degree-2 phase state → the uniform average over upper-triangular A of the acceptance probability on |ψ_A⟩; reason: the paper's ensemble (§3.2)
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 5.9, Eq. (106), p. 42 (L as in Eq. (103), p. 41)

import Definitions.Def_StabTestMem_avgDev
import Definitions.Def_StabTestMem_sigmaP
import Definitions.Def_StabTestMem_phaseAvg
import Definitions.Def_StabTestMem_phaseState

namespace StabTestMem

open QAlgorithms

/-- **Theorem 5.9: degree-2 phase states versus the maximally mixed state.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 5.9,
p. 42: "Let t < n, then E_{x∼P_mm}[|L(x) − 1|] ≤ 2^{2−(n−k−7t)/2}. (106) Consequently, t = Ω(n − k)
is required to distinguish between a random degree two phase state and the maximally mixed state."
Here `L(x) = P_{σ_P}(x)/P_mm(x)` (Eq. (103), p. 41; Eq. (109), p. 42).

(1) For every adaptive protocol with `k` memory qubits and `t < n` copies,
`E_{x∼P_mm}|L(x) − 1| ≤ 2^{2−(n−k−7t)/2}`. (2) There is `c > 0` such that every such protocol (any
`n, k, t`) whose acceptance probabilities on `ρ_mm` and on a uniformly random degree-2 phase state
differ by at least `1/3` uses `t ≥ c(n − k)` copies.

**Formalization Note.** In (2), "distinguish" (success `≥ 2/3` on each hypothesis) is generalized to
an acceptance gap `≥ 1/3`, which it implies. The acceptance probability on the random phase state
is the uniform average over upper-triangular `A` of the acceptance probability on `|ψ_A⟩`. The
constant `c` is uniform in `n, k, t` and the protocol. -/
theorem phase_vs_mixed :
    (∀ (n k t : ℕ) (X : Type) [Fintype X] (P : MemProtocol n k t X), t < n →
      avgDev P (sigmaP n t) ≤ (2 : ℝ) ^ (2 - ((n : ℝ) - k - 7 * t) / 2)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ (n k t : ℕ) (X : Type) [Fintype X] (P : MemProtocol n k t X),
      1 / 3 ≤ |P.acceptProbOp (rhoMM n t) -
          phaseAvg (fun A => P.acceptProb (ObliviousRSP.pureState (phaseState A)))| →
        c * ((n : ℝ) - k) ≤ t) := by sorry

end StabTestMem
