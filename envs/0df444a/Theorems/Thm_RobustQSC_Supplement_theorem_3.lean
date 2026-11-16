-- Prove2me | Theorems.Thm_RobustQSC_Supplement_theorem_3
-- name    : RobustQSC.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:11:59.489365+00:00
-- url     : https://prove2.me/theorems/40d3be29-3d50-4ddf-9ad7-671cefdbb1c7
-- title:
--   Theorem 3 — soundness of Protocol 1 without $o(1)$: $2\,\mathrm{Tr}[A_\psi\rho]\le 2-c(1-\langle\psi|\rho|\psi\rangle)$
-- statement:
--   Let $|\psi\rangle$ be a Haar-random $n$-qubit target state. For $j\in[n]$ and a basis $B\in\{X,Z\}$, measuring all qubits except the $j$-th of $|\psi\rangle$ (resp. of the lab state $\rho$) in basis $B$ with outcome $b\in\{0,1\}^{n-1}$ leaves the post-measurement states $|\psi^{(j,B)}_b\rangle$ (resp. $\rho^{(j,B)}_b$) on qubit $j$; $\mathrm{Meas}(\rho,B,[n]\setminus j)$ is the outcome distribution on $\rho$.
--
--   There are universal constants $c>0$ and $c_0>0$ and an $n_0$ such that for every $n\ge n_0$, with probability at least $1-2^{-c_0n}$ over $|\psi\rangle$, every density matrix $\rho$ satisfies
--   $$\mathop{\mathbb E}_{\substack{j\sim[n]\\ x\sim\mathrm{Meas}(\rho,X,[n]\setminus j)}}\langle\psi^{(j,X)}_x|\rho^{(j,X)}_x|\psi^{(j,X)}_x\rangle+\mathop{\mathbb E}_{\substack{j\sim[n]\\ z\sim\mathrm{Meas}(\rho,Z,[n]\setminus j)}}\langle\psi^{(j,Z)}_z|\rho^{(j,Z)}_z|\psi^{(j,Z)}_z\rangle\ \le\ 2-c\big(1-\langle\psi|\rho|\psi\rangle\big).$$
--
--   The left side is twice the acceptance probability $\mathrm{Tr}[A_\psi\rho]$ of the one-shot test (Protocol 1), so the theorem says that the test rejects with probability at least $\frac c2(1-\langle\psi|\rho|\psi\rangle)$, with no $o(1)$ loss: the soundness of Theorem 1 without its error term.
--
--   **Formalization Note** The left side is stated as $2\,\mathrm{Re}\,\mathrm{Tr}[A_\psi\rho]$ with $A_\psi$ the published acceptance operator `accOp ψ`; the two expressions agree term by term. Where an outcome has probability $0$ on $|\psi\rangle$ the paper's $\psi_b$ is undefined and `accOp` uses $0$; this happens only on a Haar-null set. The bad set does not depend on $\rho$.
--
--   Differences from the source:
--   - encoding: E_{j, x∼Meas(ρ,X,[n]∖j)}⟨ψ_x^{(j,X)}|ρ_x^{(j,X)}|ψ_x^{(j,X)}⟩ + E_{j, z∼Meas(ρ,Z,[n]∖j)}⟨ψ_z^{(j,Z)}|ρ_z^{(j,Z)}|ψ_z^{(j,Z)}⟩ → 2 * effectProb (accOp ψ) ρ = 2·Re Tr[A_ψ ρ], A_ψ the published accOp; reason: p.9: Pr[accept] = ½(the sum) and Pr[accept] = Tr[Aρ]; each expectation is Σ_b Tr[(|b⟩⟨b|_{[n]∖j} ⊗ |ψ_b⟩⟨ψ_b|_j)ρ], which is the corresponding half of A (§4, p.20)
--   - encoding: post-measurement state ψ_b of an outcome b that has probability 0 on |ψ⟩ (undefined) → that term of accOp is 0; reason: such outcomes exist only for ψ in a Haar-null set (ψ vanishes nowhere almost surely), so the event changes only on a null set
--   - encoding: with all but 2^{−Ω(n)} probability over Haar-random |ψ⟩, for all lab states ρ, …; c > 0 universal → ∃ c > 0, ∃ c₀ > 0, ∃ n₀, ∀ n ≥ n₀: haarTargetLaw n {ψ | IsState ψ ∧ ∃ ρ, IsDensityMatrix ρ ∧ 2 − c(1 − ⟨ψ|ρ|ψ⟩) < LHS} ≤ 2^{−c₀ n}; reason: same pinning as the base mission's Theorem 1 and Proposition 4; the ∀ ρ sits inside the bad event so the bad set does not depend on ρ; lab states are density matrices
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Theorem 3, p.9 (Pr[accept] display and Pr[accept] = Tr[Aρ], p.9; A defined in §4, p.20)

import Definitions.Def_RobustQSC_accOp
import Definitions.Def_QAlgorithms_Defs_HaarTargetStates

namespace RobustQSC.Supplement

open QAlgorithms QAlgorithms.TwoBasisCertification MeasureTheory RobustQSC

/-- **Theorem 3.** With all but `2^{−Ω(n)}` probability over a Haar-random target state `|ψ⟩`, for
all lab states `ρ`,
`E_{j∼[n], x∼Meas(ρ,X,[n]∖j)} ⟨ψ^{(j,X)}_x|ρ^{(j,X)}_x|ψ^{(j,X)}_x⟩
  + E_{j∼[n], z∼Meas(ρ,Z,[n]∖j)} ⟨ψ^{(j,Z)}_z|ρ^{(j,Z)}_z|ψ^{(j,Z)}_z⟩ ≤ 2 − c(1 − ⟨ψ|ρ|ψ⟩)`,
where `c > 0` is a universal constant.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Theorem 3, p.9 (the display
"Pr[accept] = ½(…)" and "Pr[accept] = Tr[Aρ]" on p.9; `A` defined in §4, p.20).

**Formalization Note.**
1. The left-hand side is the sum of the two expectations on p.9, which equals `2 · Pr[accept]`
   (p.9: `Pr[accept] = ½(…)`) and `Pr[accept] = Tr[Aρ]` (p.9, §4 p.20). Expanding each expectation
   as `Σ_b p_b ⟨ψ_b|ρ_b|ψ_b⟩ = Σ_b Tr[(|b⟩⟨b|_{[n]∖j} ⊗ |ψ_b⟩⟨ψ_b|_j) ρ]` gives exactly
   `2 · Re Tr[A_ψ ρ] = 2 * effectProb (accOp ψ) ρ`, with `A_ψ` the published `accOp ψ`.
2. Zero fibre: where `ψ`'s post-measurement vector is `0` the paper's `ψ_b` is undefined and
   `accOp` sets that term to `0`; such outcomes occur only on a Haar-null set of `ψ`.
3. `c` and the `Ω(n)` constant `c₀` are chosen before `n`, for `n ≥ n₀`; the bad set is the set of
   unit `ψ` for which **some** density matrix `ρ` violates the bound, so it does not depend on `ρ`.
   There is no `o(1)` term. `⟨ψ|ρ|ψ⟩ = effectProb (pureDensity ψ) ρ`. -/
theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      haarTargetLaw n {ψ | IsState ψ ∧ ∃ ρ : Matrix (Qubits n) (Qubits n) ℂ,
          IsDensityMatrix ρ ∧
          2 - c * (1 - effectProb (pureDensity ψ) ρ) < 2 * effectProb (accOp ψ) ρ}
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ * n))) := by sorry

end RobustQSC.Supplement
