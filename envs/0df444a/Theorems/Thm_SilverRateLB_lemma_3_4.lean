-- Prove2me | Theorems.Thm_SilverRateLB_lemma_3_4
-- name    : SilverRateLB.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:02.667753+00:00
-- url     : https://prove2.me/theorems/c8dba4ea-b67c-4200-a2de-abeeb3aa5fc6
-- title:
--   Lemma 3.4 — maximizing schedules exist; $\varnothing$ and a singleton are tight
-- statement:
--   Let $c>0$ and $2\le a\le\Lambda$. For every $n\ge1$ the supremum
--   $$U_n(\Lambda):=\sup_{H\in[0,\infty)^n}V_\Lambda(H)$$
--   is finite and attained. At every maximizing schedule $H$ (one with $V_\Lambda(H)=U_n(\Lambda)$), the empty set is tight and some singleton $\{t\}$ is admissible and tight.
--
--   Equality of the empty-set and singleton costs at a maximizing schedule gives the identities (16) used in Lemma 3.5.
--
--   **Formalization Note** "Finite" is boundedness above of the set of values $V_\Lambda(H)$, "attained" is a schedule whose value dominates every other of the same length, and a maximizing schedule is any such schedule.
--
--   Differences from the source:
--   - generalization: a, c of Lemma 2.4 with 0 < ε < 1/2, γ > 0 (§3.2, §B) → any constants with 0 < c, 2 ≤ a; reason: the argument uses only these properties; the paper's constants satisfy a ≥ 2 and c > 1, so the statement specializes to the source's
--   - encoding: U_n(Λ) finite and attained; maximizing schedule → BddAbove of the values; ∃ H with V H' ≤ V H for all H'; tightness for every such H; reason: same statements without forming the supremum
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma 3.4, p. 14; proof §B.2, pp. 26–28

import Mathlib
import Definitions.Def_SilverRateLB_V

namespace SilverRateLB

/-- **Lemma 3.4 (maximizing schedules).** For every `n ≥ 1` and `Λ ≥ a`, the supremum
`U_n(Λ) = sup_{H ∈ [0,∞)^n} V_Λ(H)` is finite and attained. At every maximizing schedule, the
empty set and a singleton are tight.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma 3.4, p. 14 (proof §B.2, pp. 26–28).

**Formalization Note** "Finite" is `BddAbove` of the set of values; "attained" is a schedule `H`
with `V_Λ(H') ≤ V_Λ(H)` for every `H'` of the same length; a maximizing schedule is any such `H`,
and for it `∅` and some `{t}` are tight (`{t}` tight includes `1 ≤ t ≤ n`, `h_t > 2`). The
constants `a, c` are parameters with `c > 0`, `a ≥ 2`; the paper's satisfy them. -/
theorem lemma_3_4 (a c Λ : ℝ) (hc : 0 < c) (ha : 2 ≤ a) (hΛ : a ≤ Λ) (n : ℕ) (hn : 1 ≤ n) :
    BddAbove {v : ℝ | ∃ H : List ℝ, H.length = n ∧ (∀ h ∈ H, 0 ≤ h) ∧ V a c Λ H = v} ∧
    (∃ H : List ℝ, H.length = n ∧ (∀ h ∈ H, 0 ≤ h) ∧
      ∀ H' : List ℝ, H'.length = n → (∀ h ∈ H', 0 ≤ h) → V a c Λ H' ≤ V a c Λ H) ∧
    (∀ H : List ℝ, H.length = n → (∀ h ∈ H, 0 ≤ h) →
      (∀ H' : List ℝ, H'.length = n → (∀ h ∈ H', 0 ≤ h) → V a c Λ H' ≤ V a c Λ H) →
      IsTight a c Λ H ∅ ∧ ∃ t : ℕ, IsTight a c Λ H {t}) := by sorry

end SilverRateLB
