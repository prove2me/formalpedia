-- Prove2me | Theorems.Thm_ShadowTomography_QuantumLB_theorem_19
-- name    : ShadowTomography.QuantumLB.theorem_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:11:45.389772+00:00
-- url     : https://prove2.me/theorems/ed951fb8-74dd-4302-85c9-40db6ba4a16a
-- title:
--   Theorem 19 — shadow tomography needs $\Omega(\min\{D^2,\log M\}/\varepsilon^2)$ copies
-- statement:
--   **Theorem 19.** Any strategy for shadow tomography — estimating $\operatorname{Tr}(E_i\rho)$ to within additive error $\varepsilon$ for all $i\in[M]$, with success probability at least $2/3$ — requires $\Omega\bigl(\min\{D^2,\log M\}/\varepsilon^2\bigr)$ copies of the $D$-dimensional mixed state $\rho$.
--
--   Precisely: there are a universal constant $c>0$ and a threshold $N_0$ such that for all $D, M\in\mathbb N$ and $\varepsilon$ with
--
--   $$
--   D \ge N_0,\qquad \log_2 M \ge N_0^2,\qquad 0<\varepsilon\le\tfrac16,
--   $$
--
--   there exist two-outcome measurements $E_1,\dots,E_M$ on $\mathbb C^D$ with the following property. Let a strategy consist of $k\in\mathbb N$, a measurement $\{\Pi_\omega\}_{\omega\in\Omega}$ of $\rho^{\otimes k}$ with finitely many outcomes, and outputs $b(\omega)=(b_1(\omega),\dots,b_M(\omega))\in\mathbb R^M$. If for every $D$-dimensional mixed state $\rho$
--
--   $$
--   \Pr_{\omega}\Bigl[\,\bigl|b_i(\omega)-\operatorname{Tr}(E_i\rho)\bigr|\le\varepsilon \text{ for all } i\in[M]\Bigr] \ge \frac23 ,
--   $$
--
--   then
--
--   $$
--   k \ge c\,\frac{\min\{D^2,\ \log_2 M\}}{\varepsilon^2}.
--   $$
--
--   This is the general (quantum) lower bound for Problem 1, quadratic in the dimension $D$ where the classical special case gives only $\min\{D,\log M\}$; letting $M$ grow, it recovers the $\Omega(D^2/\varepsilon^2)$ lower bound for full tomography.
--
--   **Formalization Note**
--   1. The measurements $E_i$ are chosen before the strategy and depend only on $D$, $M$, $\varepsilon$; the bound then holds for every strategy that succeeds on every mixed state.
--   2. $\Omega(\cdot)$ is a universal constant $c$ with a threshold $N_0$ on $D$ and on $\sqrt{\log_2 M}$; without a threshold the statement fails (for $D=1$ the state is known and $k=0$ suffices). The base of $\log M$ only changes $c$.
--   3. $\varepsilon\le\tfrac16$ is added: for $\varepsilon\ge\tfrac12$ the constant output $b_i=\tfrac12$ succeeds with $k=0$, so some upper limit on $\varepsilon$ is needed, and $\tfrac16$ is where the paper's construction is defined.
--   4. Problem 1's requirement $b_i\in[0,1]$ is omitted; clipping outputs to $[0,1]$ never moves them away from $\operatorname{Tr}(E_i\rho)\in[0,1]$, so the statement is equivalent.
--   5. The success probability $2/3$ is the paper's "(say) $2/3$".
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 23, Theorem 19 (with Problem 1, p. 2)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_ClassicalLB_tensorPow
import Definitions.Def_ShadowTomography_QuantumLB_POVM

namespace ShadowTomography.QuantumLB

/-- Theorem 19: for some universal `c > 0` and threshold `N₀`, whenever `D ≥ N₀`,
`log₂ M ≥ N₀²` and `0 < ε ≤ 1/6`, there are `M` two-outcome measurements on `ℂ^D` such that
every measurement of `ρ^{⊗k}` whose outputs estimate all `Tr(E_i ρ)` to within `ε` with
probability at least `2/3`, for every mixed state `ρ`, uses `k ≥ c · min{D², log₂ M}/ε²`. -/
theorem theorem_19 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (D M : ℕ) (ε : ℝ),
      N₀ ≤ D → (N₀ : ℝ) ^ 2 ≤ Real.logb 2 M → 0 < ε → ε ≤ 1 / 6 →
      ∃ E : Fin M → Matrix (Fin D) (Fin D) ℂ, (∀ i, ShadowTomography.UpperBound.IsEffect (E i)) ∧
        ∀ (k : ℕ) (Ω : Type) [Fintype Ω]
          (P : POVM Ω (Fin k → Fin D)) (b : Ω → Fin M → ℝ),
          (∀ ρ : Matrix (Fin D) (Fin D) ℂ, WildeQIT.IsDensityOperator ρ →
            (2 / 3 : ℝ) ≤ P.prob (ShadowTomography.ClassicalLB.tensorPow ρ k)
              (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε)) →
          c * min ((D : ℝ) ^ 2) (Real.logb 2 M) / ε ^ 2 ≤ (k : ℝ) := by sorry

end ShadowTomography.QuantumLB
