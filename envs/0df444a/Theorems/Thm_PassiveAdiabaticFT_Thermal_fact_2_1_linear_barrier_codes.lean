-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_fact_2_1_linear_barrier_codes
-- name    : PassiveAdiabaticFT.Thermal.fact_2_1_linear_barrier_codes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:51.898181+00:00
-- url     : https://prove2.me/theorems/7bd58781-5fae-4218-a85b-8543eacc77a9
-- title:
--   §3.2 (3.43)–(3.47) from Fact 2.1 item 3 — linear-barrier LDPC codes at every block length scale
-- statement:
--   There are constants $c'>0$, $\nu,w\in\mathbb N$ and $\rho\ge1$ such that for every $L\ge1$ there is a stabilizer code on $b$ qubits, $L\le b\le\rho L$, with $k\ge1$ logical qubits, every check of weight at most $w$, every qubit in at most $\nu$ checks, and logical energy barrier
--   $$\Delta_b\ge c'Jb\qquad\text{(for every }J>0\text{)},$$
--   equivalently: every single-qubit Pauli path to a nontrivial logical Pauli passes a syndrome with at least $c'b/2$ violated checks.
--
--   This is the form in which the proof of Theorem 3.5 uses Fact 2.1 item 3: the quantum Tanner codes of [LZ22] have a linear barrier [WB24, Section V.B, Lemma 7] and block lengths $b_i=\Theta(q^{3i})$, so a block size $C\log R$ can be rounded up to an available length at a constant-factor cost (p. 26).
--
--   Differences from the source:
--   - reading: the quantum Tanner family of [LZ22] has a linear barrier [WB24, Lemma 7] (Fact 2.1 item 3), with block lengths b_i = Θ(q^{3i}) (p. 26) → there exist c′, ν, w, ρ and for every L ≥ 1 a stabilizer code of length b ∈ [L, ρL] with k ≥ 1, check weight ≤ w, qubit degree ≤ ν and 2·barrier count ≥ c′ b; reason: this is the statement the proof of Theorem 3.5 uses at (3.43)–(3.47); the Tanner construction is not formalized on the platform, and the c₁ = 1 clause of item 3 is not used by the goal
--   - encoding: Δ_b ≥ c′ J b → c′ b ≤ 2 · barrierCount; reason: Δ_b = 2J · barrierCount and J > 0 cancels
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 12, Fact 2.1 item 3, as used in the proof of Theorem 3.5 at (3.43)–(3.47), pp. 25–26

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_CodeBlock

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- §3.2, (3.43)–(3.47), resting on Fact 2.1 item 3 (pp. 12, 26): a family of stabilizer codes
with a linear energy barrier, bounded check weight and qubit degree, and block lengths at every
scale up to a bounded ratio (the quantum Tanner codes of [LZ22] with the barrier of [WB24]).
In violated checks, `Δ_b ≥ c' J b` reads `2 · barrierCount ≥ c' b`. -/
theorem fact_2_1_linear_barrier_codes :
    ∃ c' : ℝ, 0 < c' ∧ ∃ ν w : ℕ, ∃ ρ : ℝ, 1 ≤ ρ ∧ ∀ L : ℝ, 1 ≤ L →
      ∃ (b : ℕ) (C : StabCode b), L ≤ b ∧ (b : ℝ) ≤ ρ * L ∧
        (∀ a, C.checkWeight a ≤ w) ∧ (∀ q, C.qubitDegree q ≤ ν) ∧
        c' * b ≤ 2 * C.barrierCount := by sorry

end PassiveAdiabaticFT.Thermal
