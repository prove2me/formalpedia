-- Prove2me | Theorems.Thm_ProactiveUpgrade_lemma_A_2
-- name    : ProactiveUpgrade.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:31.582004+00:00
-- url     : https://prove2.me/theorems/dfe5d287-467d-4383-87b7-a6053497ab00
-- title:
--   Lemma A.2 — the chained form (A.2) of anti-multimodularity
-- statement:
--   A function $f$ on $\mathbb N^n$ is anti-multimodular with respect to $\mathcal F$ if and only if
--
--   $$
--   f(x+a_1+\dots+a_l)+f(x+a_{l+1}+\dots+a_k)\le f(x)+f(x+a_1+\dots+a_k)\qquad\text{(A.2)}
--   $$
--
--   for all distinct $a_1,\dots,a_k\in\mathcal F$ and $0<l<k$, at every $x$ for which the four points of (A.2) lie in $\mathbb N^n$.
--
--   Differences from the source:
--   - reading: Lemma A.2 for f : ℤᵐ → ℝ and all x ∈ ℤᵐ → f on ℕⁿ; (A.2) whenever its four points x, x + a₁ + ⋯ + a_l, x + a_{l+1} + ⋯ + a_k, x + a₁ + ⋯ + a_k lie in ℕⁿ; reason: the quadrant reading of Definition A.1 (see AntiMultimodular); only the four printed points are constrained, not the intermediate grid points, which is the full-strength quadrant statement
--   - encoding: distinct a₁, …, a_k ∈ 𝓕 → an injective family a : Fin k → ℤⁿ with values in gens n; the first l and the last k − l members summed; reason: Lean convention; same instances
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Lemma A.2, p.31

import Mathlib
import Definitions.Def_ProactiveUpgrade_Dir
import Definitions.Def_ProactiveUpgrade_Gen
import Definitions.Def_ProactiveUpgrade_AntiMultimodular

namespace ProactiveUpgrade

/-- **Lemma A.2** (Chen et al., SSRN 3777846, p.31). `f` is anti-multimodular with respect to `𝓕`
iff
`f(x + a₁ + ⋯ + a_l) + f(x + a_{l+1} + ⋯ + a_k) ≤ f(x) + f(x + a₁ + ⋯ + a_k)`  (A.2)
for any distinct `a₁, …, a_k ∈ 𝓕` and `0 < l < k`.

**Formalization Note** On the quadrant: (A.2) is required whenever its four points lie in `ℕⁿ`. -/
theorem lemma_A_2 {n : ℕ} (f : (Fin n → ℕ) → ℝ) :
    AntiMultimodular f ↔
      ∀ (k l : ℕ) (a : Fin k → (Fin n → ℤ)), (∀ j, a j ∈ gens n) → Function.Injective a →
        0 < l → l < k → ∀ x : Fin n → ℤ,
          InQuad x →
          InQuad (x + ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < l), a j) →
          InQuad (x + ∑ j ∈ Finset.univ.filter (fun j : Fin k => l ≤ j.val), a j) →
          InQuad (x + ∑ j, a j) →
            liftZ f (x + ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < l), a j) +
                liftZ f (x + ∑ j ∈ Finset.univ.filter (fun j : Fin k => l ≤ j.val), a j) ≤
              liftZ f x + liftZ f (x + ∑ j, a j) := by sorry

end ProactiveUpgrade
