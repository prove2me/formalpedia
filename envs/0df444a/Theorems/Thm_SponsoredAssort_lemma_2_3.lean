-- Prove2me | Theorems.Thm_SponsoredAssort_lemma_2_3
-- name    : SponsoredAssort.lemma_2_3
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:53:00.769047+00:00
-- url     : https://prove2.me/theorems/0fd5ea3c-3e67-439a-9bbd-3bb1f14a60b8
-- title:
--   Lemma 2.3 — taxation property: an IC mechanism charges the same for the same assortment
-- statement:
--   Let $m=(S(\cdot),p(\cdot))$ be a deterministic mechanism satisfying (IC). Fix a profile $v\in\mathbb R^n_+$ and a seller $i$. For every report $v_i'\ge0$ with
--
--   $$
--   S(v_i',v_{-i})=S(v_i,v_{-i})\quad\text{we have}\quad p_i(v_i',v_{-i})=p_i(v_i,v_{-i}).
--   $$
--
--   So, with the others' reports fixed, an IC mechanism's payment for seller $i$ depends only on the assortment displayed. This is what allows (1) to describe an IC mechanism by a menu of assortment prices.
--
--   Differences from the source:
--   - generalization: $v_i'\ne v_i$ → no such hypothesis; reason: the claim is trivial when $v_i'=v_i$
--   - reading: right-hand side $p(v_i',v_{-i})$ → $p_i(v_i',v_{-i})$; reason: typo: the lemma concerns seller $i$'s payment
--   - generalization: revenues $r_1\ge\dots\ge r_n>0$ and $n\ge1$ sellers (standing, p.9) → any real revenues and any $n$; reason: the proof uses only (IC); the statement specializes to the standing setting
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Lemma 2.3, p.13

import Mathlib
import Definitions.Def_SponsoredAssort_IsIC

open scoped NNReal

namespace SponsoredAssort

/-- **Lemma 2.3 (Taxation property)** (Balseiro, Désir, *Incentive-Compatible Assortment
Optimization for Sponsored Products*, SSRN 3821382 (Feb. 21, 2022), p.13). Let `m = (S(v), p(v))`
satisfy (IC). Fix `v ∈ ℝⁿ₊` and a seller `i`. For every report `v'ᵢ` with
`S(v'ᵢ, v₋ᵢ) = S(vᵢ, v₋ᵢ)` we have `pᵢ(v'ᵢ, v₋ᵢ) = pᵢ(vᵢ, v₋ᵢ)`.

**Formalization Note.** `(v'ᵢ, v₋ᵢ)` is `Function.update v i y`. The printed right-hand side
`p(v'ᵢ, v₋ᵢ)` is `pᵢ(v'ᵢ, v₋ᵢ)`. The printed hypothesis `v'ᵢ ≠ vᵢ` is dropped (the claim is trivial
when `v'ᵢ = vᵢ`). No hypothesis on the revenues is needed. -/
theorem lemma_2_3 {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) (hIC : IsIC r m) (v : Attr n)
    (i : Fin n) (y : ℝ≥0) (hS : m.alloc (Function.update v i y) = m.alloc v) :
    m.pay (Function.update v i y) i = m.pay v i := by sorry

end SponsoredAssort
