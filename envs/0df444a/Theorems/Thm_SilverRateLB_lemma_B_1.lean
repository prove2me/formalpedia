-- Prove2me | Theorems.Thm_SilverRateLB_lemma_B_1
-- name    : SilverRateLB.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:58.341276+00:00
-- url     : https://prove2.me/theorems/5034e2a2-eeaa-4063-889a-d27367faf5e9
-- title:
--   Lemma B.1 — log-submodularity of the checkpoint cost; tight sets form a lattice
-- statement:
--   Let $c>0$ and $2\le a\le\Lambda$. For any schedule $H\in[0,\infty)^n$ and any two admissible checkpoint sets $S,T$,
--   $$Q_\Lambda(S;H)\,Q_\Lambda(T;H)\ \ge\ Q_\Lambda(S\cap T;H)\,Q_\Lambda(S\cup T;H).\tag{35}$$
--   If $S$ and $T$ are disjoint and nonempty, the inequality is strict. Consequently tight sets are closed under unions and intersections, and two nonempty tight sets cannot be disjoint.
--
--   This lattice structure is what makes the intersection of all (nonempty) tight sets tight in the proof of Lemma 3.4.
--
--   Differences from the source:
--   - generalization: a, c of Lemma 2.4 with 0 < ε < 1/2, γ > 0 (§3.2, §B) → any constants with 0 < c, 2 ≤ a; reason: the argument uses only these properties; the paper's constants satisfy a ≥ 2 and c > 1, so the statement specializes to the source's
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n → H : List ℝ with nonnegative entries, n = H.length; reason: same schedules
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma B.1, (35), p. 26

import Mathlib
import Definitions.Def_SilverRateLB_V

namespace SilverRateLB

/-- **Lemma B.1 (log-submodularity).** For any schedule `H ∈ [0,∞)^n` and admissible checkpoint
sets `S, T`, `Q_Λ(S; H) Q_Λ(T; H) ≥ Q_Λ(S ∩ T; H) Q_Λ(S ∪ T; H)` (35). If `S` and `T` are disjoint
and nonempty, the inequality is strict. Consequently, tight sets are closed under unions and
intersections, and two nonempty tight sets cannot be disjoint.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma B.1, (35), p. 26.

**Formalization Note** The constants `a, c` are parameters with `c > 0`, `2 ≤ a ≤ Λ` (the standing
`Λ ≥ a` of §B, p. 26); the paper's satisfy them. -/
theorem lemma_B_1 (a c Λ : ℝ) (hc : 0 < c) (ha : 2 ≤ a) (hΛ : a ≤ Λ) (H : List ℝ)
    (hH : ∀ h ∈ H, 0 ≤ h) (S T : Finset ℕ) (hS : IsAdmissible H S) (hT : IsAdmissible H T) :
    ckptCost a c Λ H (S ∩ T) * ckptCost a c Λ H (S ∪ T) ≤
        ckptCost a c Λ H S * ckptCost a c Λ H T ∧
    (Disjoint S T → S.Nonempty → T.Nonempty →
      ckptCost a c Λ H (S ∩ T) * ckptCost a c Λ H (S ∪ T) <
        ckptCost a c Λ H S * ckptCost a c Λ H T) ∧
    (IsTight a c Λ H S → IsTight a c Λ H T →
      IsTight a c Λ H (S ∪ T) ∧ IsTight a c Λ H (S ∩ T)) ∧
    (IsTight a c Λ H S → IsTight a c Λ H T → S.Nonempty → T.Nonempty → ¬ Disjoint S T) := by sorry

end SilverRateLB
