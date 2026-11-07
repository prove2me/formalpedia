-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_17
-- name    : RandOrderSort.lemma_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:59.82887+00:00
-- url     : https://prove2.me/theorems/30be12a8-8dd4-4311-a619-d226d7bda79e
-- title:
--   Lemma 4.17 — convex combination of crossings
-- statement:
--   Let the keys have a fixed strict order and associated nondecreasing real values $x_{(1)}\le\dots\le x_{(n)}$. If $\mathrm{OPT}(X)=x_{(n)}-x_{(1)}>0$, then every placement satisfies
--   $$\rho(A)=\sum_{a=1}^{n-1}w_aC_a,\qquad w_a=\frac{x_{(a+1)}-x_{(a)}}{\mathrm{OPT}(X)},\qquad w_a\ge 0,\qquad \sum_aw_a=1.$$
--   Consequently,
--   $$\mathbb E[e^{\theta\rho(A)}]\le\sup_a\mathbb E[e^{\theta C_a}].$$
--
--   Weighting each crossing count by the corresponding numerical gap thus recovers the ratio from the rank cuts, with no independence of the crossing counts.
--
--   **Formalization Note** Items with values $v$ carry their 0-based ranks $r$ in the strict key order, along which the values are nondecreasing, and a placement is any bijection $e$ from cells to items.
--
--   Differences from the source:
--   - encoding: sup over 1 ≤ a < n → `∃ a` with 1 ≤ a < n attaining the bound; reason: a supremum of finitely many numbers is attained, and OPT > 0 forces n ≥ 2
--   - generalization: the expectation for the paper's fixed θ > 0 and the random placement of the algorithm → every real θ and every probability law `p` on placements; reason: convexity of the exponential needs no sign, and the algorithm's placement law is one such p
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.17, p.38

import Mathlib
import Definitions.Def_RandOrderSort_OnlineCmpAlg

namespace RandOrderSort

/-- **Lemma 4.17 (Convex combination of crossings)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.38: "Let the keys have a fixed strict
order and associated nondecreasing real values x_(1) ≤ · · · ≤ x_(n). If OPT(X) = x_(n) − x_(1) > 0,
then every placement satisfies ρ(A) = ∑_{a=1}^{n−1} w_a C_a, w_a = (x_(a+1) − x_(a))/OPT(X), w_a ≥ 0,
∑_a w_a = 1. Consequently, E[e^{θρ(A)}] ≤ sup_a E[e^{θC_a}]."

**Formalization Note.** Items `Fin n` with values `v` carry a strict key order given by their 0-based
ranks `r`, along which the values are nondecreasing; `x_(a)` is the value of the item of 1-based rank
`a` (`ordVal v r (a − 1)`). A placement is any bijection `e` (cell `↦` item), with ratio `placeRatio`
(as (1)) and crossings `placeCa`. The second part holds for every probability law `p` on placements
(a finite space) and every real `θ` (the paper's `θ` is a fixed positive constant); the supremum over
`1 ≤ a < n` of finitely many numbers is attained, so it is stated as `∃ a`. -/
theorem lemma_4_17 : ∀ (n : ℕ) (v : Fin n → ℝ) (r : Fin n ≃ Fin n),
    (∀ i j, r i < r j → v i ≤ v j) → 0 < OPT v →
      (∀ e : Equiv.Perm (Fin n),
        placeRatio v e = ∑ a ∈ Finset.Ico 1 n,
          (ordVal v r a - ordVal v r (a - 1)) / OPT v * (placeCa r e a : ℝ)) ∧
      (∀ a ∈ Finset.Ico 1 n, 0 ≤ (ordVal v r a - ordVal v r (a - 1)) / OPT v) ∧
      ∑ a ∈ Finset.Ico 1 n, (ordVal v r a - ordVal v r (a - 1)) / OPT v = 1 ∧
      ∀ (θ : ℝ) (p : PMF (Equiv.Perm (Fin n))), ∃ a, 1 ≤ a ∧ a < n ∧
        ∑ e, (p e).toReal * Real.exp (θ * placeRatio v e) ≤
          ∑ e, (p e).toReal * Real.exp (θ * (placeCa r e a : ℝ)) := by sorry

end RandOrderSort
