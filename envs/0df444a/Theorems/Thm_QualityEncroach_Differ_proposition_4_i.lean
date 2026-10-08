-- Prove2me | Theorems.Thm_QualityEncroach_Differ_proposition_4_i
-- name    : QualityEncroach.Differ.proposition_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:26.628117+00:00
-- url     : https://prove2.me/theorems/dd976bbd-8683-4aa9-be5b-6d8e5f2505ba
-- title:
--   Proposition 4(i) and Table 1, p. 16 — thresholds c₁ < c₂: differentiate for c < c₁, uniform quality for c₁ < c < c₂, no encroachment for c > c₂
-- statement:
--   Fix $k>0$ and consider the encroachment game with quality differentiation (§5). There are thresholds $0<c_1<c_2$, depending only on $k$, such that for every $c\ge0$ an equilibrium exists and every subgame-perfect equilibrium, with manufacturer's choice $(w^*,u^*,t^*)$ and direct quantity $q^*_M$ on the path, satisfies:
--
--   1. if $0\le c<c_1$:
--   $$
--   t^*=\frac65-\frac25\sqrt{4-\frac{5c}{ku^{*2}}}<1,\qquad u^*>\sqrt{\frac{4c}{3k}},\qquad q^*_M>0;
--   $$
--   2. if $c_1<c<c_2$:
--   $$
--   t^*=1,\qquad u^*<\sqrt{\frac{4c}{3k}},\qquad q^*_M>0;
--   $$
--   3. if $c>c_2$: $q^*_M=0$.
--
--   For small direct selling costs the encroaching manufacturer sells a lower quality through the retailer; for intermediate costs she prefers uniform quality; for large costs she does not use the direct channel.
--
--   **Formalization Note.** Table 1 writes the middle row as $c_1<c\le c_2$. The point $c=c_2$ is left out, as in Claim 2, because the paper's sources disagree on it; $c=c_1$ is excluded by the table itself.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 16, Proposition 4(i) and Table 1 (proof: pp. 30–32)

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game

namespace QualityEncroach.Differ

theorem proposition_4_i (k : ℝ) (hk : 0 < k) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ c1 < c2 ∧
      ∀ c : ℝ, 0 ≤ c →
        (∃ σ : Profile, IsSPE k c (Set.Ioi 0) σ) ∧
        ∀ σ : Profile, IsSPE k c (Set.Ioi 0) σ →
          (c < c1 →
            σ.t = 6 / 5 - 2 / 5 * Real.sqrt (4 - 5 * c / (k * σ.u ^ 2)) ∧ σ.t < 1 ∧
            Real.sqrt (4 * c / (3 * k)) < σ.u ∧ 0 < σ.path.qM) ∧
          (c1 < c → c < c2 →
            σ.t = 1 ∧ σ.u < Real.sqrt (4 * c / (3 * k)) ∧ 0 < σ.path.qM) ∧
          (c2 < c → σ.path.qM = 0) := by sorry

end QualityEncroach.Differ
