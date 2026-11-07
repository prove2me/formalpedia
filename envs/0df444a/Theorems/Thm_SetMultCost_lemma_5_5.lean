-- Prove2me | Theorems.Thm_SetMultCost_lemma_5_5
-- name    : SetMultCost.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:40.318207+00:00
-- url     : https://prove2.me/theorems/413f773c-0bd9-4646-b5d7-cec2f2c0e912
-- title:
--   Lemma 5.5 (corrected: $a_j,b_j\in\mathbb N$ in $m$-good) — an $m$-good $(\tau,S)$ for restricted circuits
-- statement:
--   Let $\mathbf r\in(\mathbb N\cup\{\infty\})^\Delta$, let $\alpha\in(0,1)$ with $\alpha\ge\frac12$ have convergent denominators $q_0,q_1,\dots$, let $m\ge0$ be real and $\kappa\ge1$ an integer. Define $\tau_0=1$ and
--
--   $$\tau_i=\min\big(r_i\tau_{i-1},\ \lfloor 6m\cdot\kappa\,q_hq_{h-1}\rfloor\big)\quad\text{where }h=\min\{j:\tau_{i-1}<2q_j/3\}.$$
--
--   Let $S\subseteq[\Delta]$ be the coordinates with $\tau_i<r_i\tau_{i-1}$. Then $\alpha$ is $m$-good for $(\tau,S)$.
--
--   The page's formula has $\kappa=2$, while Lemma 7.3 needs $\kappa=1$. The floor is exact whenever the page's $\tau$ is integer-valued, in particular for every integer $m$.
--
--   Differences from the source:
--   - generalization: the factor 2 in 6m·2q_hq_{h−1} → any integer κ ≥ 1; reason: κ = 2 is the print; the proof and Lemma 7.3 use κ = 1
--   - correction: m-good with positive integers a_j, b_j → m-good with a_j, b_j ∈ ℕ; reason: see Lemma 4.4; the proof here says "non-negative positive"
--   - generalization: τ_i = min(r_iτ_{i−1}, 6m·2q_hq_{h−1}) for a parameter m ≥ 0, an integer sequence only when 6m·2q_hq_{h−1} ∈ ℕ (Definitions 4.1, 4.3) → the floor ⌊6m·κq_hq_{h−1}⌋ for every real m ≥ 0; reason: the floor is exact on every instance where the printed τ is integer-valued, so the page's lemma is the special case
--   - reading: α with continued fraction → `IsCFValue`, an infinite expansion; reason: as in Fact 5.2; it also makes h exist
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Lemma 5.5, p.18

import Mathlib
import Definitions.Def_SetMultCost_cfDen
import Definitions.Def_SetMultCost_thresholdSeq
import Definitions.Def_SetMultCost_IsTauSProduct
import Definitions.Def_SetMultCost_IsMGood

namespace SetMultCost

/-- **Lemma 5.5.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.18: "Let r = (r1, · · · , r∆) ∈ (N ∪ ∞)^∆, α ∈ (0, 1) with α ≥ 1/2, and let
{q0, q1, . . .} be the convergent denominators of α. For a parameter m ≥ 0, define the following
sequence τ0 = 1, for all 1 ≤ i ≤ ∆, τi = min (riτi−1, 6m · 2qhqh−1) where h = min {j : τi−1 <
2qj/3}. Let S = {i1, . . . , iℓ} ⊆ [∆] be the coordinates where τi < riτi−1. Then, α is m-good for
(τ,S)."

**Formalization Note.** `κ` replaces the printed factor `2`. The page's statement is `κ = 2`, its proof
and Lemma 7.3 use `κ = 1`, and every `κ ≥ 1` holds. `m ≥ 0` is real, as printed; `thresholdSeq`
takes the floor of `6m · κ · q_h q_{h−1}`, which is exact whenever the printed `τ` is integer-valued. -/
theorem lemma_5_5 (r : ℕ → ℕ∞) (a : ℕ → ℤ) (α : ℝ) (h : IsCFValue a α) (hα : 1 / 2 ≤ α) (hα1 : α < 1)
    (m : ℝ) (hm : 0 ≤ m) (κ : ℕ) (hκ : 1 ≤ κ) (Δ : ℕ) :
    IsMGood α m (thresholdSeq r a m κ) (tauS Δ r (thresholdSeq r a m κ)) := by sorry

end SetMultCost
