-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_lemma_14
-- name    : ShadowTomography.UpperBound.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:08.246781+00:00
-- url     : https://prove2.me/theorems/ac9dd5db-f320-4be6-bfe0-1d5b04415f96
-- title:
--   Lemma 14 (Quantum OR Bound) — distinguish max_i Tr(E_iρ) ≥ c from ≤ c − ε with O(log(1/δ) log M/ε²) copies
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $\rho$ be an unknown mixed state of any finite dimension, let $E_1,\dots,E_M$ ($M\ge2$) be known two-outcome measurements, and let $c\in\mathbb R$, $\varepsilon>0$ and $0<\delta<1$. Suppose we are promised that either
--
--   1. there exists $i\in[M]$ with $\mathrm{Tr}(E_i\rho)\ge c$, or else
--   2. $\mathrm{Tr}(E_i\rho)\le c-\varepsilon$ for all $i\in[M]$.
--
--   Then there are a number of copies
--   $$
--   k \le C\,\frac{\log(1/\delta)}{\varepsilon^2}\,\log M
--   $$
--   and a two-outcome measurement $A$ on $\rho^{\otimes k}$ (depending on the $E_i$, $c$, $\varepsilon$, $\delta$, but not on $\rho$) that accepts with probability at least $1-\delta$ in case 1 and with probability at most $\delta$ in case 2.
--
--   The number of copies does not depend on the dimension of the system. This lemma is the decision step that Gentle Search (Lemma 15) turns into a search.
--
--   **Formalization Note** The constant $C$ is quantified before the dimension, so $k$ is independent of it. Two hypotheses are added: $M\ge2$ (at $M=1$ the bound $\log M=0$ forces $k=0$, and with no copy a single unknown $\mathrm{Tr}(E_1\rho)$ cannot be compared with $c$), and $\delta<1$ (for $\delta\ge 1/2$ the claim is trivial). Logarithms are natural; the base only changes $C$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, pp. 13–14, Lemma 14

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- **Lemma 14 (Quantum OR Bound).** There is a universal constant `C` such that for every finite
dimension, every `M ≥ 2` known two-outcome measurements `E i`, every threshold `c`, gap `ε > 0`
and failure probability `δ ∈ (0, 1)`, some `k ≤ C · (log(1/δ)/ε²) · log M` and some two-outcome
measurement `A` on `ρ^{⊗k}` accept with probability at least `1 - δ` if some `Tr(E_i ρ) ≥ c`
and at most `δ` if every `Tr(E_i ρ) ≤ c - ε`. -/
theorem lemma_14 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (M : ℕ) (E : Fin M → Matrix n n ℂ) (c ε δ : ℝ),
        2 ≤ M → (∀ i, IsEffect (E i)) → 0 < ε → 0 < δ → δ < 1 →
        ∃ k : ℕ, (k : ℝ) ≤ C * (Real.log (1 / δ) / ε ^ 2) * Real.log M ∧
          ∃ A : Matrix (Fin k → n) (Fin k → n) ℂ, IsEffect A ∧
            ∀ ρ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ →
              ((∃ i, c ≤ ((E i) * ρ).trace.re) → 1 - δ ≤ (A * tensorPow ρ k).trace.re) ∧
              ((∀ i, ((E i) * ρ).trace.re ≤ c - ε) → (A * tensorPow ρ k).trace.re ≤ δ) := by sorry

end ShadowTomography.UpperBound
