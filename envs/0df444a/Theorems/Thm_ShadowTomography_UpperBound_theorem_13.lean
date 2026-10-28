-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_theorem_13
-- name    : ShadowTomography.UpperBound.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:44:58.273492+00:00
-- url     : https://prove2.me/theorems/22517b2b-a415-48ce-8c84-2c47660bc3b9
-- title:
--   Theorem 13 (Harrow–Lin–Montanaro) — one-copy test: accept ≥ (1−ǫ)²/7 if some Tr(E_iρ) ≥ 1−ǫ, ≤ 4ΔM if ΣTr(E_iρ) ≤ ΔM
-- statement:
--   Let $E_1,\dots,E_M$ be known two-outcome measurements on a finite-dimensional system, and let $\epsilon\le 1/2$ and $\Delta$ be reals. There is a single two-outcome measurement $T$ (depending on the $E_i$, $\epsilon$ and $\Delta$ only) such that for every mixed state $\rho$:
--
--   1. if there is an $i\in[M]$ with $\mathrm{Tr}(E_i\rho)\ge 1-\epsilon$, then
--   $$
--   \mathrm{Tr}(T\rho) \ge \frac{(1-\epsilon)^2}{7};
--   $$
--   2. if $\mathrm{Tr}(E_1\rho)+\cdots+\mathrm{Tr}(E_M\rho)\le \Delta M$, then $\mathrm{Tr}(T\rho)\le 4\Delta M$.
--
--   This is the "quantum OR" test of Harrow, Lin and Montanaro, which Aaronson's Theorem 13 restates; its proof is in their paper, not in Aaronson's. It is the one-copy primitive from which the Quantum OR Bound (Lemma 14) is obtained by amplification.
--
--   **Formalization Note** "A test that uses one copy of $\rho$" is a two-outcome measurement $T$ on the same system; a test using an ancilla induces such a $T$. The hypothesis $\epsilon\le1/2$ is not printed in Aaronson's restatement but is a hypothesis of the source result (Harrow–Lin–Montanaro, arXiv:1607.03236, Corollary 11, "fix parameters $\epsilon\le 1/2$, $\delta$"); without some such bound the statement is false (with $E_i=0$, $\Delta=0$, $\epsilon=3$, both cases hold for every $\rho$). Harrow et al. state it for projectors; general effects reduce to projectors by a Naimark dilation with an ancilla. The paper's $\epsilon$ is written `ε` in Lean.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 13, Theorem 13 (= Harrow, Lin, Montanaro, arXiv:1607.03236, Corollary 11)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- **Theorem 13 (Harrow, Lin, and Montanaro; their Corollary 11).** For known two-outcome
measurements `E 0, …, E (M-1)` and parameters `ε ≤ 1/2` and `Δ`, there is a single two-outcome
test `T` on one copy of the state that accepts with probability at least `(1-ε)^2/7` whenever
some `E i` accepts with probability at least `1 - ε`, and with probability at most `4ΔM`
whenever the acceptance probabilities sum to at most `ΔM`. -/
theorem theorem_13 {n : Type} [Fintype n] [DecidableEq n] (M : ℕ)
    (E : Fin M → Matrix n n ℂ) (ε Δ : ℝ) (hE : ∀ i, IsEffect (E i)) (hε : ε ≤ 1 / 2) :
    ∃ T : Matrix n n ℂ, IsEffect T ∧
      ∀ ρ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ →
        ((∃ i, 1 - ε ≤ ((E i) * ρ).trace.re) → (1 - ε) ^ 2 / 7 ≤ (T * ρ).trace.re) ∧
        (∑ i, ((E i) * ρ).trace.re ≤ Δ * M → (T * ρ).trace.re ≤ 4 * Δ * M) := by sorry

end ShadowTomography.UpperBound
