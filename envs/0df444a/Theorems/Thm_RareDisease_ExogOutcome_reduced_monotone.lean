-- Prove2me | Theorems.Thm_RareDisease_ExogOutcome_reduced_monotone
-- name    : RareDisease.ExogOutcome.reduced_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:17.619526+00:00
-- url     : https://prove2.me/theorems/6dfcfdd9-f017-4eab-97fe-fe7b566b3e31
-- title:
--   §4.4, p. 15, after (20) — welfare and expenditure of (20) are increasing in α and in β
-- statement:
--   Let $k>0$ and $p\in(0,1)$, and write
--   $$W(\alpha,\beta)=\frac{p\,(1-(1-\beta)p)^3}{4(1-\alpha)k},\qquad M(\alpha,\beta)=\frac{\alpha p^2(1-(1-\beta)p)^2}{4(1-\alpha)^2k}+\frac{\beta p^2(1-(1-\beta)p)^2}{2(1-\alpha)k}$$
--   for the patient welfare and the government's expenditure of the reduced problem (20). Then:
--
--   1. for each fixed $\beta\in[0,1)$, $\alpha\mapsto W(\alpha,\beta)$ is strictly increasing on $[0,1)$;
--   2. for each fixed $\alpha\in[0,1)$, $\beta\mapsto W(\alpha,\beta)$ is strictly increasing on $[0,1)$;
--   3. for each fixed $\beta\in[0,1)$, $\alpha\mapsto M(\alpha,\beta)$ is strictly increasing on $[0,1)$;
--   4. for each fixed $\alpha\in[0,1)$, $\beta\mapsto M(\alpha,\beta)$ is strictly increasing on $[0,1)$.
--
--   Monotonicity in both subsidies is what forces an optimal policy onto the curve where the budget constraint binds.
--
--   **Formalization Note** The page says "increasing"; the strict version is stated because it holds for $p\in(0,1)$ and is what the binding-budget argument uses.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 15, §4.4, sentence after (20)

import Mathlib

namespace RareDisease.ExogOutcome

/-- §4.4, p. 15, after (20): the patient welfare
`W(α, β) = p (1 - (1 - β) p)³ / (4 (1 - α) k)` and the government's expenditure
`M(α, β) = α p² (1 - (1 - β) p)² / (4 (1 - α)² k) + β p² (1 - (1 - β) p)² / (2 (1 - α) k)`
of (20) are strictly increasing in `α ∈ [0,1)` for every fixed `β ∈ [0,1)`, and strictly
increasing in `β ∈ [0,1)` for every fixed `α ∈ [0,1)`. -/
theorem reduced_monotone (k p : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
      StrictMonoOn (fun α : ℝ => p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α) * k))
        (Set.Ico (0 : ℝ) 1)) ∧
    (∀ α ∈ Set.Ico (0 : ℝ) 1,
      StrictMonoOn (fun β : ℝ => p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α) * k))
        (Set.Ico (0 : ℝ) 1)) ∧
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
      StrictMonoOn (fun α : ℝ => α * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
          + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α) * k))
        (Set.Ico (0 : ℝ) 1)) ∧
    (∀ α ∈ Set.Ico (0 : ℝ) 1,
      StrictMonoOn (fun β : ℝ => α * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
          + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α) * k))
        (Set.Ico (0 : ℝ) 1)) := by sorry

end RareDisease.ExogOutcome
