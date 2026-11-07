-- Prove2me | Theorems.Thm_RobustQSC_theorem_1_constant_robustness
-- name    : RobustQSC.theorem_1_constant_robustness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:02.966737+00:00
-- url     : https://prove2.me/theorems/23511bdd-8c90-4305-8d81-86e419ba0f4a
-- title:
--   Theorem 1, p.3 — constant robustness with single-qubit measurements
-- statement:
--   There exists an efficient protocol using single-qubit measurements, namely Protocol 1, that, for all but a $2^{-\Omega(n)}$ fraction of pure $n$-qubit target states $|\psi\rangle$, satisfies the following. Given oracle access to a classical description of $|\psi\rangle$ (Definition 1), and a single copy of an $n$-qubit mixed state $\rho$:
--
--   1. **Completeness.** It accepts with probability at least $\langle\psi|\rho|\psi\rangle$.
--   2. **Soundness.** It rejects with probability at least
--
--   $$
--   \frac{1-\langle\psi|\rho|\psi\rangle}{C}-o(1),
--   $$
--
--   for a universal constant $C>1$.
--
--   Moreover, the single-qubit measurements are either all in the $X$ basis or all in the $Z$ basis, except for one final (non-Pauli) adaptive measurement.
--
--   The fraction of targets is one set, independent of $\rho$: outside it both guarantees hold for every $\rho$. This answers Conjecture 1 of Coladangelo, Li, Slote and Wu: constant robustness is attainable for almost all targets with single-qubit measurements alone.
--
--   Differences from the source:
--   - generalization: "there exists an efficient protocol" → the named tree `protocol1 n`, with a run of at most $n+4$ oracle reads, coins and single-qubit measurements and an explicit $2\times2$ classical computation; reason: §4 (p.20) states that the paper proves it for Protocol 1; the existence claim follows by taking this witness
--   - reading: "the single-qubit measurements are either all in the $X$-basis or all in the $Z$-basis, except for one final … measurement" → `TwoBasisShape`: along each run, a bulk in one of the two bases, then at most one further measurement; reason: Protocol 1 samples the basis, so the choice is per run
--   - reading: Step 4 of Protocol 1 on a zero post-measurement vector (undefined) → reject; reason: null for a Haar-random target
--   - encoding: "fraction of pure target states" → the outer measure under the published `haarTargetLaw` of the unit vectors for which the guarantee fails for some density matrix, at most $2^{-c_0n}$ for $n\ge n_0$; reason: the failure set does not depend on $\rho$, as in the printed order of quantifiers
--   - encoding: $o(1)$, universal $C>1$ → one sequence $e_n\to0$ and one constant $C>1$ chosen before $n$; reason: the standard meaning
--   - encoding: $\langle\psi|\rho|\psi\rangle$ → `effectProb (pureDensity ψ) ρ`; reason: same quantity
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Theorem 1, p.3 (restated p.20); Protocol 1, p.6; Definition 1, pp.7–8

import Definitions.Def_RobustQSC_protocol1
import Definitions.Def_QAlgorithms_Defs_HaarTargetStates

namespace RobustQSC

open QAlgorithms QAlgorithms.TwoBasisCertification MeasureTheory Filter Topology

/-- **Theorem 1 (Constant robustness with single-qubit measurements).** There is an efficient
protocol using single-qubit measurements, namely Protocol 1, that, for all but a `2^{−Ω(n)}`
fraction of pure `n`-qubit target states `|ψ⟩`, given Definition-1 oracle access to `|ψ⟩` and one
copy of an `n`-qubit mixed state `ρ`, accepts with probability at least `⟨ψ|ρ|ψ⟩` (completeness) and
rejects with probability at least `(1 − ⟨ψ|ρ|ψ⟩)/C − o(1)` for a universal constant `C > 1`
(soundness); moreover its single-qubit measurements are all in the `X` basis or all in the `Z`
basis, except for one final adaptive measurement.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Theorem 1, p.3 (restated p.20: "the paper
will focus on proving that Protocol 1 satisfies Theorem 1"); Protocol 1, p.6; Definition 1, pp.7–8.

**Formalization Note.**
1. The printed "there exists an efficient protocol" is witnessed by the named tree `protocol1 n`,
   which implies the existence statement. Its run has `n + 4` steps (two coins, `n − 1` bulk
   measurements, two oracle reads, one final measurement) and its classical computation between
   nodes is the explicit `2 × 2` formula of `holdoutVec` and `unitaryOfCol`.
2. "All but a `2^{−Ω(n)}` fraction": for `n ≥ n₀`, the Haar measure (`haarTargetLaw`) of the
   set of unit vectors `ψ` for which the guarantee fails for **some** density matrix `ρ` is at
   most `2^{−c₀ n}`; the bad set does not depend on `ρ`.
3. `o(1)` is one sequence `e n → 0` and `C > 1` one constant, both chosen before `n`.
4. `⟨ψ|ρ|ψ⟩ = effectProb (pureDensity ψ) ρ = Re Tr(|ψ⟩⟨ψ|ρ)`. The "Moreover" clause is
   `TwoBasisShape`. -/
theorem theorem_1_constant_robustness :
    ∃ (C : ℝ) (e : ℕ → ℝ) (c₀ : ℝ) (n₀ : ℕ),
      1 < C ∧ 0 < c₀ ∧ Tendsto e atTop (𝓝 0) ∧
      (∀ n, 1 ≤ n → (protocol1 n).StepsAtMost (n + 4) ∧ (protocol1 n).TwoBasisShape) ∧
      ∀ n, n₀ ≤ n →
        haarTargetLaw n {ψ | IsState ψ ∧ ¬ ∀ ρ : Matrix (Qubits n) (Qubits n) ℂ,
            IsDensityMatrix ρ →
              effectProb (pureDensity ψ) ρ ≤ (protocol1 n).outProb ψ ρ true ∧
              (1 - effectProb (pureDensity ψ) ρ) / C - e n ≤ (protocol1 n).outProb ψ ρ false}
          ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ * n))) := by sorry

end RobustQSC
