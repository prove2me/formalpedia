-- Prove2me | Theorems.Thm_SluggishCapability_Myopic_part_ii_recurrent
-- name    : SluggishCapability.Myopic.part_ii_recurrent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:10.86315+00:00
-- url     : https://prove2.me/theorems/15854688-a257-4605-86b6-2ef78c459030
-- title:
--   Proof of part (ii), p. 20 — the two-state program's extended chain has recurrent states exactly (2µ − 1, L), (2µ, H)
-- statement:
--   Let $\mu \ge 1$ be an integer, $\beta \in (0,1)$ and $M \ge 2\mu$. Consider the extended (capability, state) chain of the two-state program ($\Pr(L \to H) = 1$, $\Pr(H \to L) = \beta$, $\Pr(H \to H) = 1 - \beta$, $f(L) = 0$, $f(H) = 2\mu$) under the myopic rule (2), with capability in $\{0,\dots,M\}$. Then
--
--   1. its recurrent states are exactly $(2\mu - 1, L)$ and $(2\mu, H)$;
--   2. it has an invariant distribution;
--   3. every invariant distribution $\nu$ satisfies
--   $$\nu(2\mu, H) = \frac{1}{1+\beta}, \qquad \nu(2\mu - 1, L) = \frac{\beta}{1+\beta}.$$
--
--   Both masses tend to $1/2$ as $\beta \to 1$, which is the paper's description of the invariant capability distribution in the limit.
--
--   **Formalization Note** Index `0` is $L$ and index `1` is $H$. The paper's "best-reply (given by Step 1)" refers to rule (2).
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), p. 20, proof of Proposition 1(ii)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace SluggishCapability.Myopic

/-- Proof of part (ii), p. 20. For `β ∈ (0, 1)` and any truncation `M ≥ 2µ`, the extended chain
of the two-state program (index `0` is `L`, `1` is `H`) has exactly two recurrent states,
`(2µ − 1, L)` and `(2µ, H)`; it has an invariant distribution, and every invariant distribution
puts mass `1/(1 + β)` on `(2µ, H)` and `β/(1 + β)` on `(2µ − 1, L)`. -/
theorem part_ii_recurrent (μ : ℕ) (hμ : 1 ≤ μ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (M : ℕ) (hM : 2 * μ ≤ M) :
    (∀ x : Fin (M + 1) × Fin 2, IsRecurrentState (extKernel (twoStateP β) (twoStateF μ) M) x ↔
      (((x.1 : ℕ) = 2 * μ - 1 ∧ x.2 = 0) ∨ ((x.1 : ℕ) = 2 * μ ∧ x.2 = 1))) ∧
    (∃ ν : Fin (M + 1) × Fin 2 → ℝ, IsStationary (extKernel (twoStateP β) (twoStateF μ) M) ν) ∧
    ∀ ν : Fin (M + 1) × Fin 2 → ℝ, IsStationary (extKernel (twoStateP β) (twoStateF μ) M) ν →
      ∀ x : Fin (M + 1) × Fin 2,
        ((x.1 : ℕ) = 2 * μ → x.2 = 1 → ν x = 1 / (1 + β)) ∧
        ((x.1 : ℕ) = 2 * μ - 1 → x.2 = 0 → ν x = β / (1 + β)) := by sorry

end SluggishCapability.Myopic
