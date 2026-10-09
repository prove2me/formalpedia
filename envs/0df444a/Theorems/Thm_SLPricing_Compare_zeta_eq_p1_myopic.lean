-- Prove2me | Theorems.Thm_SLPricing_Compare_zeta_eq_p1_myopic
-- name    : SLPricing.Compare.zeta_eq_p1_myopic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:55.843991+00:00
-- url     : https://prove2.me/theorems/6d28e2d5-20f3-471c-bbaa-40960bf2b7bc
-- title:
--   Proof of Lemma 4, Step 3, p. 32 — for $\delta_c = 0$ the responsive purchasing threshold is $\zeta(p_1) = p_1$
-- statement:
--   Consider the mission's model with myopic consumers, $\delta_c = 0$, and any $\gamma \ge 0$. Under responsive pricing, fix a first-period price $p_1 \in [0,1]$. Then
--   1. the first-period buyer set $B = [p_1,1]$ together with the second-period rule $s(q_u) = p_2^*(q_u, p_1)$ of (6) is an equilibrium continuation: $s$ is optimal for the remaining types $[0,p_1)$ at every $q_u$, and $B$ is a purchasing equilibrium given $s$;
--   2. in every equilibrium continuation $(B', s')$ after $p_1$, the buyer set $B'$ coincides with $[p_1,1]$ up to a null set.
--
--   In the paper's terms, the threshold $\zeta(p_1)$ solving the indifference equation (9) equals $p_1$ when $\delta_c = 0$. With the pre-announced counterpart this shows that at $\delta_c = 0$ both pricing regimes generate the same first-period sales and the same reviews for the same $p_1$.
--
--   **Formalization Note** The hypothesis $p_1 \in [0,1]$ is added, as for the pre-announced threshold. Uniqueness is up to null sets. Part 1 uses Lemma 3 with $\bar x = p_1$.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Appendix A, proof of Lemma 4, Step 3, p. 32

import Mathlib
import Definitions.Def_SLPricing_Compare_Model
import Definitions.Def_SLPricing_Resp_P2Star
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Compare

/-- Appendix A, proof of Lemma 4, Step 3, p. 32: for `δc = 0` the first-period purchasing
threshold under responsive pricing is `ζ(p₁) = p₁` for every `p₁ ∈ [0, 1]`: `[p₁, 1]` together
with the second-period rule (6) for `x̄ = p₁` is a subgame-perfect continuation, and in every such
continuation the set of first-period buyers equals `[p₁, 1]` up to a null set. -/
theorem zeta_eq_p1_myopic (P : Params) (hP : P.Standing) (hδ : P.δc = 0)
    (p₁ : ℝ) (hp₁ : p₁ ∈ Icc (0 : ℝ) 1) :
    IsRespEq P p₁ (Icc p₁ 1) (fun q => SLPricing.Resp.p2Star P.c q p₁) ∧
      ∀ (B : Set ℝ) (s : ℝ → ℝ), IsRespEq P p₁ B s → B =ᵐ[volume] Icc p₁ 1 := by sorry

end SLPricing.Compare
