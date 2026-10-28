-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_lemma_15
-- name    : ShadowTomography.UpperBound.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:11.608433+00:00
-- url     : https://prove2.me/theorems/04532e33-cf69-4504-88a8-e00aafe6be0e
-- title:
--   Lemma 15 (Gentle Search) — find j with Tr(E_jρ) ≥ c − ε from O(log⁴M/ε² · (log log M + log 1/δ)) copies
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $\rho$ be an unknown mixed state of any finite dimension, let $E_1,\dots,E_M$ ($M\ge1$) be known two-outcome measurements, and let $c\in\mathbb R$, $\varepsilon>0$ and $0<\delta\le 1/2$. Then there are a number of copies
--   $$
--   k \le C\,\frac{\log^4 M}{\varepsilon^2}\Big(\log\log M + \log\frac1\delta\Big)
--   $$
--   and a measurement of $\rho^{\otimes k}$ with outcomes $j\in[M]$ (depending on the $E_i$, $c$, $\varepsilon$, $\delta$, but not on $\rho$) such that, whenever there exists $i\in[M]$ with $\mathrm{Tr}(E_i\rho)\ge c$, the outcome $j$ satisfies $\mathrm{Tr}(E_j\rho)\ge c-\varepsilon$ with probability at least $1-\delta$.
--
--   Gentle Search is the subroutine that, inside each iteration of the main procedure, locates a measurement on which the current hypothesis is wrong.
--
--   **Formalization Note** The constant $C$ is quantified before the dimension. Added hypotheses: $M\ge1$ (with $M=0$ there is no measurement with outcomes in the empty set), and $\delta\le 1/2$, which keeps the factor $\log\log M+\log(1/\delta)$ positive at $M=2$ ($\log\log 2<0$). Logarithms are natural; for $\log\log$ the base matters only through the constant and the additive shift covered by $\delta\le1/2$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 14, Lemma 15 (proof pp. 14–15)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- **Lemma 15 (Gentle Search).** There is a universal constant `C` such that for every finite
dimension, every `M ≥ 1` known two-outcome measurements `E i`, every `c`, `ε > 0` and
`δ ∈ (0, 1/2]`, some `k ≤ C (log⁴ M / ε²)(log log M + log(1/δ))` and some measurement of
`ρ^{⊗k}` with an index `j` as outcome output, for every state with some `Tr(E_i ρ) ≥ c`, an
index with `Tr(E_j ρ) ≥ c - ε` with probability at least `1 - δ`. -/
theorem lemma_15 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (M : ℕ) (E : Fin M → Matrix n n ℂ) (c ε δ : ℝ),
        1 ≤ M → (∀ i, IsEffect (E i)) → 0 < ε → 0 < δ → δ ≤ 1 / 2 →
        ∃ k : ℕ, (k : ℝ) ≤ C * (Real.log M ^ 4 / ε ^ 2) *
            (Real.log (Real.log M) + Real.log (1 / δ)) ∧
          ∃ P : POVM (Fin M) (Fin k → n),
            ∀ ρ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ →
              (∃ i, c ≤ ((E i) * ρ).trace.re) →
                1 - δ ≤ P.prob (tensorPow ρ k) (fun j => c - ε ≤ ((E j) * ρ).trace.re) := by sorry

end ShadowTomography.UpperBound
