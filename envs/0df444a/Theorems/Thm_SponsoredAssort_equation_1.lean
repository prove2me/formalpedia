-- Prove2me | Theorems.Thm_SponsoredAssort_equation_1
-- name    : SponsoredAssort.equation_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:53:10.237019+00:00
-- url     : https://prove2.me/theorems/476ced57-f020-4ef4-ab5f-3eeaa9b51914
-- title:
--   Equation (1) — an IC allocation maximizes seller $i$'s utility over the menu $\{p_S(v_{-i})\}$
-- statement:
--   Let $m$ satisfy (IC), let $i$ be a seller and fix the others' attractiveness $v_{-i}$. Then there are prices $\{p_S(v_{-i})\}_{S\in\mathrm{supp}_i(m,v_{-i})}$ such that seller $i$ pays $p_{S(v_i,v_{-i})}(v_{-i})$ whenever it reports $v_i$, and for every $v_i\ge0$
--
--   $$
--   S(v_i,v_{-i})\in\arg\max_{S\in\mathrm{supp}_i(m,v_{-i})}\Big\{r_i\,\pi_i\big(S,(v_i,v_{-i})\big)-p_S(v_{-i})\Big\}.
--   $$
--
--   This is the counterpart of the envelope formula: payments pin down the allocation, each seller selecting its preferred assortment from a menu.
--
--   Differences from the source:
--   - encoding: prices indexed by $S\in\mathrm{supp}_i(m,v_{-i})$ → a price function on all assortments, whose values outside the support are unused; reason: same menu
--   - generalization: revenues $r_1\ge\dots\ge r_n>0$ and $n\ge1$ sellers (standing, p.9) → any real revenues and any $n$; reason: the proof uses only (IC); the statement specializes to the standing setting
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2.3, (1), p.14

import Mathlib
import Definitions.Def_SponsoredAssort_IsIC
import Definitions.Def_SponsoredAssort_supp

open scoped NNReal

namespace SponsoredAssort

/-- **Equation (1)** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), §2.3, p.14). If `m`
satisfies (IC), then for every seller `i` and every `v₋ᵢ` there are payments
`{p_S(v₋ᵢ)}_{S ∈ suppᵢ(m, v₋ᵢ)}` such that seller `i` pays `p_{S(vᵢ)}(v₋ᵢ)` and
`S(vᵢ) ∈ argmax_{S ∈ suppᵢ(m, v₋ᵢ)} {rᵢ · πᵢ(S, (vᵢ, v₋ᵢ)) − p_S(v₋ᵢ)}` for every `vᵢ`.

**Formalization Note.** `v₋ᵢ` is fixed through `v`; the attractiveness `vᵢ` of seller `i` ranges
over `y : ℝ≥0` via `Function.update v i y`. The menu `p` is a function on all assortments, of which
only its values on `suppᵢ(m, v₋ᵢ)` matter. -/
theorem equation_1 {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) (hIC : IsIC r m) (v : Attr n)
    (i : Fin n) :
    ∃ p : Finset (Fin n) → ℝ,
      (∀ y : ℝ≥0, m.pay (Function.update v i y) i = p (m.alloc (Function.update v i y))) ∧
      ∀ y : ℝ≥0, ∀ T ∈ supp m i v,
        r i * choiceProb T (Function.update v i y) i - p T ≤
          r i * choiceProb (m.alloc (Function.update v i y)) (Function.update v i y) i -
            p (m.alloc (Function.update v i y)) := by sorry

end SponsoredAssort
