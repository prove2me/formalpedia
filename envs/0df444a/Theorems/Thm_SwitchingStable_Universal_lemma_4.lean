-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_4
-- name    : SwitchingStable.Universal.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:27.560331+00:00
-- url     : https://prove2.me/theorems/b35595b0-7c25-4497-a0bd-0cdb2706c4f1
-- title:
--   Lemma 4 — Motion lemma
-- statement:
--   Fix stable matchings $\mu,\nu$, a man $u$ with current stable index $q$, and a different valid stable index $r$. Set $p=\mu(v_r)$. The motion lemma states
--   $$r>q,\ \operatorname{idx}_u(\nu)\ge r\Longrightarrow \mu(p)\succ_p\nu(p),$$
--   $$r<q,\ \operatorname{idx}_u(\nu)\le r\Longrightarrow \nu(p)\succ_p\mu(p).$$
--   These are strict comparisons in both directions and describe the motion forced on the current owner of a boundary partner.
--
--   Differences from the source:
--   - encoding: Stable-list indices and inverse owners → Zero-based finite lists with valid natural indices, and the actual inverse bijection; reason: Preserves every valid boundary and both strict comparison directions.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 4, PDF p. 5, Lemma 4

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_4 {n : ℕ} (I : StableMatching.Instance n)
    (μ ν : StableMatching.Matching n) (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (u : Fin n) (r : ℕ) (hr : r < degree I u) (hne : r ≠ idx I μ u) :
    let p := μ.symm (atPartner I μ u r)
    (idx I μ u < r → r ≤ idx I ν u → I.manPrefers p (μ p) (ν p)) ∧
    (r < idx I μ u → idx I ν u ≤ r → I.manPrefers p (ν p) (μ p)) := by sorry

end SwitchingStable.Universal
