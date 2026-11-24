-- Prove2me | Theorems.Thm_ShockWear_RandThreshold_Supplement_theorem52c
-- name    : ShockWear.RandThreshold.Supplement.theorem52c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:01:22.317895+00:00
-- url     : https://prove2.me/theorems/34f238ec-7652-483e-a92e-8e50eb5c0e16
-- title:
--   Theorem 5.2 (c) — if P̄_k^(1/k) is decreasing for every damage law, the threshold G is IHRA
-- statement:
--   Let $G$ be a distribution with $G(0) = 0$ and $\bar G = 1 - G$. For a distribution $F$ with $F(z) = 0$ for $z < 0$ put $\bar P_k(F) = \int_0^\infty F^{(k)}(x)\, dG(x)$, $k = 0, 1, \dots$. If for **every** such $F$
--   $$\bar P_k(F)^{1/k} \text{ is decreasing in } k = 1, 2, \dots,$$
--   then $G$ is IHRA: $[\bar G(t)]^{1/t}$ is decreasing in $t > 0$.
--
--   Together with part (b), this brackets the threshold laws for which the discrete IHRA condition holds for every damage law between the IHR and the IHRA class.
--
--   **Formalization Note.** $\bar P_k$ is (5.1) as printed; for $F$ degenerate at $x_0$ it equals $\bar G(k x_0 -)$, as the paper's own proof of (c) writes. Powers are real powers with exponents $1/k$ and $1/t$; "decreasing" means non-increasing. Distributions are probability measures on $\mathbb R$.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 643, Theorem 5.2 (c)

import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.RandThreshold.Supplement

open MeasureTheory ProbabilityTheory

theorem theorem52c (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iic 0) = 0)
    (hdec : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
      ∀ j k : ℕ, 1 ≤ j → j ≤ k →
        randP μ ν k ^ (1 / (k : ℝ)) ≤ randP μ ν j ^ (1 / (j : ℝ))) :
    IsIHRA (survOf ν) := by sorry

end ShockWear.RandThreshold.Supplement
