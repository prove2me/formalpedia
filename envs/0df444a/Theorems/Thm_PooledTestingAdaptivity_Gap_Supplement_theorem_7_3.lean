-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_Supplement_theorem_7_3
-- name    : PooledTestingAdaptivity.Gap.Supplement.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:41:44.620207+00:00
-- url     : https://prove2.me/theorems/268c363f-a33e-4650-939a-6bf37e1764f7
-- title:
--   Theorem 7.3 — Boundary regimes, parts (i)–(iv)
-- statement:
--   Let $J$ be a standard-model instance with $n$ individuals and pool cap $G$, let $B$ be a budget, and suppose the optimal welfare is positive, $\mathrm{OPT}_{\mathrm{dyn}}(B,J)>0$. With $T_x$, $u^*$, $\Lambda$, $u(t)$, $\varphi_G$, $\mathrm{OPT}_{\mathrm{disj}}$ and the ratios $\mathcal A=\mathrm{OPT}_{\mathrm{dyn}}/\mathrm{OPT}_{\mathrm{stat}}$, $\mathcal A_{\mathrm{disj}}=\mathrm{OPT}_{\mathrm{dyn}}/\mathrm{OPT}_{\mathrm{disj}}$:
--
--   1. If $\Lambda\le1$, then $\mathrm{OPT}_{\mathrm{dyn}}(B,J)=\mathrm{OPT}_{\mathrm{stat}}(B,J)=\mathrm{OPT}_{\mathrm{disj}}(B,J)=T_B$; and $q_i\le1/2$ for all $i$ implies $\Lambda\le1$.
--   2. If $B=1$ or $B\ge n$, the three optimal values coincide.
--   3. If $0\le\gamma<1$ and there are $B$ pairwise disjoint pools $t_1,\dots,t_B$, each nonempty with at most $G$ members, with $u(t_b)\ge(1-\gamma)u^*$ for each $b$, then $\mathcal A(B,J)\le\mathcal A_{\mathrm{disj}}(B,J)\le1/(1-\gamma)$; if moreover $\gamma=0$, all three optimal values equal $Bu^*$.
--   4. If $q_i\ge\theta>0$ for every individual and $n\ge BG$, then
--   $$\mathcal A(B,J)\le\min\{2,\mathcal A_{\mathrm{disj}}(B,J)\}\le\min\Big\{2,\min_{s\in\{1,\dots,G\}}\frac{\max\{1,\Lambda/s\}}{\theta^{s-1}}\Big\}\le\min\{2,\varphi_G(\theta)\},\qquad\varphi_G(\theta)=\min_{s\in\{1,\dots,G\}}\frac{G}{s\,\theta^{s-1}} .$$
--
--   These regimes identify when feedback is worthless (low health probabilities, a single test, enough tests for everyone, many near-optimal disjoint pools) and bound the adaptivity gap in high-health populations.
--
--   Differences from the source:
--   - encoding: the instance has positive optimal welfare → 0 < OPT_dyn(B, J); reason: OPT_dyn, OPT_stat and OPT_disj are positive under the same condition (B ≥ 1 and some u_i > 0), so the readings coincide
--   - encoding: the ratios A and A_disj → if the denominator is 0 then 1 else the quotient; reason: the source's own 0/0 := 1 convention
--   - encoding: B pairwise disjoint pools in (iii) → a family indexed by Fin B of nonempty sets of at most G individuals, pairwise disjoint at distinct indices; reason: pools of the standard model are nonempty and of size at most G
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Theorem 7.3, Eq. (24), printed p. 24, PDF p. 25; proof printed p. 25, PDF p. 26

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Comparison

namespace PooledTestingAdaptivity.Gap.Supplement

/-- Theorem 7.3 (Boundary regimes), printed p. 24, PDF p. 25; proof printed p. 25.
All four parts, under positive optimal welfare. -/
theorem theorem_7_3 {n : ℕ} (J : Instance n) (B : ℕ)
    (hpos : 0 < optDynamic (standardFamily J B)) :
    -- (i)
    ((Lambda J ≤ 1 →
        optDynamic (standardFamily J B) = optStatic (standardFamily J B) ∧
          optStatic (standardFamily J B) = optDisj J B ∧
          optDisj J B = topSum J B) ∧
      ((∀ i, J.q i ≤ 1 / 2) → Lambda J ≤ 1)) ∧
    -- (ii)
    ((B = 1 ∨ n ≤ B) →
        optDynamic (standardFamily J B) = optStatic (standardFamily J B) ∧
          optStatic (standardFamily J B) = optDisj J B) ∧
    -- (iii)
    (∀ (γ : ℝ), 0 ≤ γ → γ < 1 → ∀ (P : Fin B → Finset (Fin n)),
        (∀ b, (P b).Nonempty ∧ (P b).card ≤ J.cap) →
        Pairwise (fun b c => Disjoint (P b) (P c)) →
        (∀ b, (1 - γ) * uStar J ≤ poolValue J (P b)) →
        ratioA J B ≤ ratioDisj J B ∧ ratioDisj J B ≤ 1 / (1 - γ) ∧
          (γ = 0 →
            optDynamic (standardFamily J B) = B * uStar J ∧
              optStatic (standardFamily J B) = B * uStar J ∧
              optDisj J B = B * uStar J)) ∧
    -- (iv)
    (∀ θ : ℝ, 0 < θ → (∀ i, θ ≤ J.q i) → B * J.cap ≤ n →
        ratioA J B ≤ min 2 (ratioDisj J B) ∧
          min 2 (ratioDisj J B) ≤ min 2 (lambdaBound J θ) ∧
          min 2 (lambdaBound J θ) ≤ min 2 (phiG J θ)) := by sorry

end PooledTestingAdaptivity.Gap.Supplement
