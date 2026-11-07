-- Prove2me | Theorems.Thm_TIEMaximin_lemma_3_11
-- name    : TIEMaximin.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:50.111149+00:00
-- url     : https://prove2.me/theorems/3776dd44-4e8f-45e5-886f-e39ae14c877c
-- title:
--   Lemma 3.11 — the low goods hold at least $a_i\,\mathrm{TPS}_i$
-- statement:
--   Let $m\ge n\ge2$, $\alpha\in(0,1)$, and let $v$ be a nonnegative profile. For every deficient agent $i$,
--
--   $$v_i(L_i)\ge a_i\,\mathrm{TPS}_i.$$
--
--   This is the pool of low-good value from which a deficient agent is compensated.
--
--   Differences from the source:
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 3.11, p.17

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Deficient

namespace TIEMaximin

/-- **Lemma 3.11** (p.17). For every deficient agent `i`, `v_i(L_i) ≥ a_i TPS_i`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 3.11, p.17.

**Formalization Note.** Stated for every `α ∈ (0,1)` (p.10). -/
theorem lemma_3_11 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (v : Fin n → Fin m → ℝ) (hv : Nonneg v) (i : Fin n) (hi : IsDeficient α v i) :
    (aDef α v i : ℝ) * tps n (v i) ≤ ∑ g ∈ low α v i, v i g := by sorry

end TIEMaximin
