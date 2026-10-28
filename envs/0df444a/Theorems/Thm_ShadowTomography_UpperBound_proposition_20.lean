-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_proposition_20
-- name    : ShadowTomography.UpperBound.proposition_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:37.074986+00:00
-- url     : https://prove2.me/theorems/69fcbb1d-f415-4258-bcba-c8c684a29385
-- title:
--   Proposition 20 — decide Tr(E_iρ) ≥ c_i vs ≤ c_i − ε for all i at once with O(log(M/δ)/ε²) copies
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $\rho$ be an unknown mixed state of any finite dimension, $E_1,\dots,E_M$ ($M\ge1$) known two-outcome measurements, $c_1,\dots,c_M\in[0,1]$, $\varepsilon>0$ and $0<\delta<1$. Suppose that for each $i\in[M]$, either $\mathrm{Tr}(E_i\rho)\ge c_i$ or $\mathrm{Tr}(E_i\rho)\le c_i-\varepsilon$. Then there are a number of copies
--
--   $$
--   k \le C\,\frac{\log(M/\delta)}{\varepsilon^2}
--   $$
--
--   and a measurement of $\rho^{\otimes k}$ with outcomes $v\in\{0,1\}^M$ (depending on the data but not on $\rho$) such that, with probability at least $1-\delta$, $v_i=1$ exactly for those $i$ with $\mathrm{Tr}(E_i\rho)\ge c_i$, for all $i\in[M]$ simultaneously.
--
--   It shows that the lower bound of Theorem 19 is matched when each measurement comes with a promise gap.
--
--   **Formalization Note** Added hypotheses: $M\ge1$ and $\delta<1$ (for $\delta\ge1/2$ the claim is trivial). Logarithms are natural.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 24, Proposition 20 (proof pp. 24–25)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- **Proposition 20.** There is a universal constant `C` such that for every finite dimension,
every `M ≥ 1` known two-outcome measurements `E i`, thresholds `c i ∈ [0, 1]`, `ε > 0` and
`δ ∈ (0, 1)`, some `k ≤ C log(M/δ)/ε²` and some measurement of `ρ^{⊗k}` with outcomes
`v : Fin M → Bool` decide, for every state satisfying the promise
"`Tr(E_i ρ) ≥ c_i` or `Tr(E_i ρ) ≤ c_i - ε` for each `i`", which case holds for every `i` at
once, with probability at least `1 - δ`. -/
theorem proposition_20 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (M : ℕ) (E : Fin M → Matrix n n ℂ)
        (c : Fin M → ℝ) (ε δ : ℝ),
        1 ≤ M → (∀ i, IsEffect (E i)) → (∀ i, c i ∈ Set.Icc (0 : ℝ) 1) → 0 < ε → 0 < δ → δ < 1 →
        ∃ k : ℕ, (k : ℝ) ≤ C * Real.log (M / δ) / ε ^ 2 ∧
          ∃ P : POVM (Fin M → Bool) (Fin k → n),
            ∀ ρ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ →
              (∀ i, c i ≤ ((E i) * ρ).trace.re ∨ ((E i) * ρ).trace.re ≤ c i - ε) →
                1 - δ ≤ P.prob (tensorPow ρ k)
                  (fun v => ∀ i, (v i = true ↔ c i ≤ ((E i) * ρ).trace.re)) := by sorry

end ShadowTomography.UpperBound
