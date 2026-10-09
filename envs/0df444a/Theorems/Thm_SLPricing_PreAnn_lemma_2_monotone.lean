-- Prove2me | Theorems.Thm_SLPricing_PreAnn_lemma_2_monotone
-- name    : SLPricing.PreAnn.lemma_2_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:53.339983+00:00
-- url     : https://prove2.me/theorems/eb481ae3-ea3c-4a74-a971-f3467e5a2660
-- title:
--   Lemma 2, p. 13 — the threshold $\theta(p_1,p_2)$ is increasing in $\gamma$, $p_1$, $\delta_c$ and decreasing in $p_2$
-- statement:
--   The first-period purchasing threshold $\theta(p_1,p_2)$ of Lemma 2 equals $1-|B|$ for any purchasing equilibrium $B$. Its monotonicity is stated jointly. Take two instances of the model with the same prior standard deviation $\sigma_p$, both satisfying the standing assumptions, with SL influence $0<\gamma\le\gamma'$ and discount factors $\delta_c\le\delta_c'$, and plans with $0\le p_1\le p_1'\le 1$ and $p_2'\le p_2$. If $B$ is a purchasing equilibrium of the first instance under $\{p_1,p_2\}$ and $B'$ one of the second under $\{p_1',p_2'\}$, then
--   $$|B'|\le|B|,\qquad\text{i.e.}\qquad \theta\le\theta'.$$
--   So $\theta$ is increasing in $\gamma$, $p_1$, $\delta_c$ and decreasing in $p_2$: social learning makes consumers "more strategic".
--
--   **Formalization Note** Monotonicity is weak. It cannot be strict in general: at $\delta_c=0$ the threshold is $p_1$ whatever $\gamma$ and $p_2$, and under adoption inertia it is constantly $1$. Varying $\gamma$ with $\sigma_p$ fixed is varying $\sigma_q$, as in the paper's proof. The unit cost does not enter the consumers' game and is not constrained.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Lemma 2 (i), last sentence, p. 13; proof, Step 4, p. 29

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Lemma 2, p. 13, monotonicity clause (proof p. 29): the first-period threshold
`θ(p₁, p₂) = 1 − (mass of first-period buyers)` is (weakly) increasing in `γ`, `p₁`, `δc` and
decreasing in `p₂`. Stated jointly for two models with the same `σp`, both with
`γ > 0` and first-period prices in `[0, 1]`: if `γ ≤ γ'`, `δc ≤ δc'`, `p₁ ≤ p₁'`, `p₂' ≤ p₂`, then
any equilibrium of the primed plan has at most the mass of any equilibrium of the unprimed one. -/
theorem lemma_2_monotone (P P' : Params) (hP : P.Standing) (hP' : P'.Standing)
    (hσ : P'.σp = P.σp) (hγ : 0 < P.γ) (hγγ : P.γ ≤ P'.γ) (hδδ : P.δc ≤ P'.δc)
    (p₁ p₂ p₁' p₂' : ℝ) (hp₁ : p₁ ∈ Icc (0 : ℝ) 1) (hp₁' : p₁' ∈ Icc (0 : ℝ) 1)
    (h₁ : p₁ ≤ p₁') (h₂ : p₂' ≤ p₂) (B B' : Set ℝ)
    (hB : IsPreEq P p₁ p₂ B) (hB' : IsPreEq P' p₁' p₂' B') :
    mass B' ≤ mass B := by sorry

end SLPricing.PreAnn
