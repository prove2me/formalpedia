-- Prove2me | Theorems.Thm_StabTestMem_Supplement_phaseState_learning_lower_bound
-- name    : StabTestMem.Supplement.phaseState_learning_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:44:35.793014+00:00
-- url     : https://prove2.me/theorems/6a9ec670-9cda-4c9d-80c2-e1049a298a77
-- title:
--   Theorem 6.6 — non-adaptive identification of a degree-2 phase state with $k$ qubits of memory needs $\Omega(n^2/(2k+\log 3))$ copies
-- statement:
--   For an upper-triangular $A\in\mathbb F_2^{n\times n}$ let $|\psi_A\rangle=2^{-n/2}\sum_x(-1)^{x^\top Ax}|x\rangle$ be the degree-2 phase state. A non-adaptive learner with $k$ qubits of memory receives $t$ copies of $|\psi_A\rangle$ and outputs an estimate $\hat A$.
--
--   There are constants $c>0$ and $n_0$ such that for all $n\ge n_0$, all $k\ge0$ and all $t$: if a non-adaptive learner with $k$ qubits of memory and $t$ copies satisfies
--   $$\frac{1}{2^{n(n+1)/2}}\sum_{A\text{ upper-triangular}}\Pr[\hat A=A]\ \ge\ \frac23,$$
--   then
--   $$t\ \ge\ c\,\frac{n^2}{2k+\log_2 3}.$$
--
--   The ensemble carries $n(n+1)/2$ bits, and each round of a non-adaptive protocol with $k$ memory qubits reveals at most $2k+\log_2 3$ bits about $A$. At $k=0$ this is the $\Omega(n^2)$ single-copy lower bound; for $k\ge1$ it gives the lower half of Theorem 1.2, since degree-2 phase states are stabilizer states.
--
--   **Formalization Note** Learners are `StabTestMem.Supplement.NALearner`, the average success probability is `StabTestMem.Supplement.phaseIdProb`, and $|\psi_A\rangle$ is the published `StabTestMem.phaseState`.
--
--   Differences from the source:
--   - generalization: identifies an unknown state from the ensemble {|ψ_A⟩} with probability ≥ 2/3 → the success probability averaged over A uniform on the upper-triangular matrices is ≥ 2/3; reason: worst-case success ≥ 2/3 implies average success ≥ 2/3, so the Lean theorem specializes to the printed one; the Fano step (Eq. (198)) uses only the average
--   - reading: non-adaptive learner → NALearner: precommitted shared randomness, then history-independent instruments, then post-processing; reason: the §6.1 notion of non-adaptive (pp. 52, 55); a fixed schedule is the one-seed case
--   - reading: Ω(n^2/(2k + log 3)) → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, ∀ k t: c·n²/(2k + log₂ 3) ≤ t; reason: asymptotic notation in n; information is measured in bits (H(A) = n(n+1)/2, p. 55), so log is log₂; the t(2k + 3) of Eq. (209) is a typo for t(2k + log 3), Eq. (206)
--   - encoding: the ensemble {|ψ_A⟩} → A uniform over upper-triangular F₂ matrices, diagonal included (the published IsUpperTri), with the published phaseState; reason: the law of A in the proof (p. 56); A ↦ ψ_A is injective on these matrices
--   - encoding: identifies an unknown state → the learner outputs an estimate Â of A and succeeds when Â = A; reason: identifying ψ_A is identifying A by injectivity, as the proof notes (p. 56)
--   - encoding: at most k qubits of coherent quantum memory → memory of exactly k qubits, every k ≥ 0; reason: a protocol with k' ≤ k memory qubits is one with k, and the bound decreases in k
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 6.6, p. 56, proof pp. 56–57 (Eqs. (198), (206), (209))

import Definitions.Def_StabTestMem_Supplement_phaseIdProb

namespace StabTestMem.Supplement

open QAlgorithms

/-- **Theorem 6.6 (non-adaptive lower bound for identifying a degree-2 phase state).** Arunachalam,
Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444
(version of 2 Nov 2026), Theorem 6.6, p. 56: "A non-adaptive learner that identifies an unknown
state from the ensemble {|ψ_A⟩} with probability ≥ 2/3, using at most k qubits of coherent
quantum memory, requires Ω(n^2/(2k + log 3)) copies."

There are `c > 0` and `n₀` such that for every `n ≥ n₀`, every `k ≥ 0`, every `t`, every finite
outcome alphabet and every non-adaptive learner (`StabTestMem.Supplement.NALearner`) with `k`
memory qubits and `t` copies that outputs an estimate `Â` of `A`, if the probability that `Â = A`,
averaged over `A` uniform on the upper-triangular `F₂` matrices with input `t` copies of `|ψ_A⟩`
(`StabTestMem.Supplement.phaseIdProb`), is at least `2/3`, then `t ≥ c n² / (2k + log₂ 3)`.

**Formalization Note.** Generalization: the success hypothesis is averaged over the uniform `A`
(what the Fano step, Eq. (198), uses), which is implied by worst-case success; and learners may use
precommitted shared randomness (`NALearner`; `m = 1` is a fixed schedule). Reading: `Ω` is
asymptotic in `n` (`∃ n₀`); `log` is `log₂` (information in bits, `H(A) = n(n+1)/2`, p. 55); the
`t(2k + 3)` of Eq. (209) is a typo for `t(2k + log 3)` (Eq. (206)). "At most k" memory qubits embeds
in exactly `k`, and the bound decreases in `k`. The learner outputs `Â` directly; `A ↦ ψ_A` is
injective on upper-triangular `A`. -/
theorem phaseState_learning_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k t : ℕ, ∀ (X : Type) [Fintype X]
      (L : NALearner n k t X (Matrix (Fin n) (Fin n) (ZMod 2))),
      2 / 3 ≤ phaseIdProb L →
        c * (n : ℝ) ^ 2 / (2 * (k : ℝ) + Real.logb 2 3) ≤ t := by sorry

end StabTestMem.Supplement
