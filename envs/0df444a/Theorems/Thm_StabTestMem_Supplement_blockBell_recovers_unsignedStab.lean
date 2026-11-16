-- Prove2me | Theorems.Thm_StabTestMem_Supplement_blockBell_recovers_unsignedStab
-- name    : StabTestMem.Supplement.blockBell_recovers_unsignedStab
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:43:21.678956+00:00
-- url     : https://prove2.me/theorems/3fb209e4-d0ba-4904-b58f-7c14b794b4f3
-- title:
--   Theorem 6.2 — block Bell sampling recovers the unsigned stabilizer group of a full-support stabilizer state with $O(n^2/k)$ copies (corrected: $n^2/\min(k,n)$ copies)
-- statement:
--   Let $|\psi\rangle$ be an $n$-qubit stabilizer state that is **full-support** (every computational-basis amplitude is nonzero), and let $M_\psi\le\mathbb F_2^{2n}$ be its unsigned stabilizer group, the Pauli labels $u$ with $P_u|\psi\rangle=\pm|\psi\rangle$.
--
--   There are absolute constants $C$ and $c>0$ such that for all $n\ge1$ and $k\ge1$ there is one fixed non-adaptive measurement schedule with $k$ qubits of memory, using
--   $$t\le C\,\frac{n^2}{\min(k,n)}$$
--   copies, together with a classical post-processing of the transcript, that outputs $M_\psi$ with probability at least
--   $$1-2^{-cn}$$
--   for every full-support stabilizer state $|\psi\rangle$.
--
--   In the paper the input is a Clifford branch $C_j|\psi\rangle$ of the unknown state, and the theorem is the label-recovery step of the $O(n^2/k)$ learner of Theorem 1.2: a random Clifford makes the state full-support with constant probability (Lemma 6.1), and the signs are recovered separately (Corollary 6.4).
--
--   **Formalization Note** The schedule is a single protocol of the published `StabTestMem.MemProtocol` with `StabTestMem.Supplement.IsNonAdaptive`, chosen before $\psi$; the success probability is `StabTestMem.Supplement.eventProb`; $M_\psi$ is `StabTestMem.Supplement.unsignedStab` and full-support is `StabTestMem.Supplement.IsFullSupport`.
--
--   Differences from the source:
--   - correction: O(n^2/k) copies (no range of k stated) → t ≤ C·n²/min(k, n) for every k ≥ 1; reason: for k ≫ n² the printed bound allows t = 0, impossible since the 2^{n(n+1)/2} > 1 full-support unsigned groups would have to be recovered from a ψ-independent output; the proof's ⌈n/k⌉ blocks give n·⌈n/k⌉ = O(n²/min(k, n)), the printed bound for k ≤ n
--   - encoding: Fix a Clifford branch j, |ψ_j⟩ = C_j|ψ⟩, M_j = C_j(M_ψ) → the input is any full-support stabilizer state ψ and the target its unsigned group M_ψ; reason: a Clifford image of a stabilizer state is a stabilizer state and M_j = M_{ψ_j} (p. 52); every full-support stabilizer state is such an image
--   - reading: failure probability 2^{−Ω(n)} → success probability ≥ 1 − 2^{−c·n} for all n ≥ 1, with C and c > 0 chosen before n and k; reason: uniform exponential decay, as the proof's Ω(n) samples per block give
--   - encoding: full-support → every computational-basis amplitude nonzero; reason: equivalent to M_ψ ∩ Z = {0} for stabilizer states (p. 52)
--   - encoding: fixed nonadaptive measurement schedule using at most k qubits of coherent memory → one non-adaptive MemProtocol n k t X with memory of exactly k qubits, and a post-processing map to sets of Pauli labels; reason: the published model; unused memory qubits embed "at most k"
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 6.2, p. 53; §6.1, p. 52

import Definitions.Def_StabTestMem_Supplement_IsNonAdaptive
import Definitions.Def_StabTestMem_Supplement_eventProb
import Definitions.Def_StabTestMem_Supplement_unsignedStab
import Definitions.Def_StabTestMem_Supplement_IsFullSupport
import Definitions.Def_QAlgorithms_Defs_StabilizerLearning

namespace StabTestMem.Supplement

open QAlgorithms

/-- **Theorem 6.2 (block Bell sampling recovers the unsigned stabilizer group of a full-support
stabilizer state).** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited
quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 6.2, p. 53: "Fix a Clifford
branch j, and write |ψ_j⟩ = C_j|ψ⟩ and M_j = C_j(M_ψ). If |ψ_j⟩ is full-support, then there is a
fixed nonadaptive measurement schedule using O(n^2/k) copies and at most k qubits of coherent
memory that recovers M_j with failure probability 2^{−Ω(n)}."

There are constants `C` and `c > 0` such that for all `n ≥ 1` and `k ≥ 1` there are a finite
outcome alphabet, a number of copies `t ≤ C n² / min(k, n)`, a non-adaptive protocol `P` of the
published `StabTestMem.MemProtocol n k t X` (deterministic: one fixed schedule) and a
post-processing map `out` from transcripts to sets of Pauli labels such that for every `n`-qubit
stabilizer state `ψ` all of whose computational-basis amplitudes are nonzero, the probability
that `out` returns the unsigned stabilizer group `M_ψ` is at least `1 − 2^{−c n}`.

**Formalization Note.** The branch is absorbed: `|ψ_j⟩` (a stabilizer state, being a Clifford image
of one) is the input, and `M_j = M_{ψ_j}` (p. 52). The schedule is chosen before `ψ`.
Correction: the paper states no range of `k`; its proof (blocks of size `≤ k`, `m = ⌈n/k⌉`)
gives `O(n · ⌈n/k⌉) = O(n²/min(k, n))`, and `O(n²/k)` for `k ≫ n²` would allow `t = 0` copies,
impossible since there are `2^{n(n+1)/2} > 1` full-support unsigned groups. `2^{−Ω(n)}` is read as
`2^{−c n}` uniformly in `n ≥ 1`, `C, c` fixed before `n, k`. "At most k" memory qubits embeds in
exactly `k` (unused qubits). -/
theorem blockBell_recovers_unsignedStab :
    ∃ C c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ∃ (X : Type) (_ : Fintype X) (t : ℕ) (P : MemProtocol n k t X)
        (out : (Fin t → X) → Set (CutRankSched.Pauli n)),
        IsNonAdaptive P ∧ (t : ℝ) ≤ C * (n : ℝ) ^ 2 / ((min k n : ℕ) : ℝ) ∧
        ∀ ψ : EuclideanSpace ℂ (Qubits n), IsStabilizerState ψ → IsFullSupport ψ →
          1 - (2 : ℝ) ^ (-(c * n)) ≤
            eventProb P (ObliviousRSP.pureState ψ) (fun x => out x = unsignedStab ψ) := by sorry

end StabTestMem.Supplement
