-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_lemma_5
-- name    : SalesRebate.NoIncreasing.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:27.228437+00:00
-- url     : https://prove2.me/theorems/f93debc8-f0d9-41d7-afd0-801e2d6c0ca8
-- title:
--   Lemma 5, p. 29 (PDF 29) — for increasing non-constant r̂ the posterior expected reward is strictly increasing in the valuation
-- statement:
--   Let $(\theta, \sigma_\theta, \sigma_\epsilon)$ be a valid model and $\hat r : \mathbb R \to [0,p]$ a reward as a function of the quality. Write $r(x) = \mathbb E_{v\mid v_i = x}[\hat r(v)]$, the expectation under the posterior $N(\tau x + (1-\tau)\theta, \sigma_v^2)$.
--
--   1. If $\hat r$ is (weakly) increasing and not constant, then $r$ is strictly increasing:
--   $$x_1 > x_2 \implies \mathbb E_{v\mid v_1}[\hat r(v)] > \mathbb E_{v\mid v_2}[\hat r(v)].$$
--   2. If $\hat r$ is (weakly) decreasing, then $r$ is decreasing.
--
--   This monotonicity of expected rewards is what makes the integral term of (9) non-positive for increasing reward programs.
--
--   **Formalization Note** The page says "increasing non-constant reward program $r(\cdot)$", but its proof works with $\hat r$, and the statement is posed on $\hat r$: a program $r$ on $[0,1]$ can be non-constant only at the endpoints $0, 1$, which the sales volume $\Phi(\cdot) \in (0,1)$ never reaches, in which case $\hat r$ is constant and the strict conclusion fails. The bound $\hat r \in [0,p]$ (from $L^\infty(\mathbb R;[0,p])$, p. 10) makes the posterior expectations finite; measurability is automatic for monotone $\hat r$. "Decreasing" is read as weakly decreasing, as on the page.
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 29, Lemma 5 (in the proof of Theorem 2)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting

namespace SalesRebate.NoIncreasing

open MeasureTheory ProbabilityTheory BlackScholesModel

theorem lemma_5 (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) :
    (Monotone rhat → (∃ a b, rhat a ≠ rhat b) → StrictMono (M.condReward rhat)) ∧
      (Antitone rhat → Antitone (M.condReward rhat)) := by sorry

end SalesRebate.NoIncreasing
