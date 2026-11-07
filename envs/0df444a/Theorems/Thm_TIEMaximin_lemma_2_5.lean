-- Prove2me | Theorems.Thm_TIEMaximin_lemma_2_5
-- name    : TIEMaximin.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:56.570407+00:00
-- url     : https://prove2.me/theorems/be8747f0-9cc7-4298-bc64-f07c4dd7d6cb
-- title:
--   Lemma 2.5 — $\mathrm{MMS}_i\le\mathrm{TPS}_i\le v_i(M)/n$, and the maximum in (2) exists
-- statement:
--   Let $n\ge1$ and let $u$ be nonnegative item values. Then
--
--   $$\mathrm{MMS}_n(u,M)\le\mathrm{TPS}_n(u,M)\le\frac{u(M)}{n},$$
--
--   and $\mathrm{TPS}_n(u,M)$ is the greatest element of $\{t\ge0:\frac1n\sum_{g\in M}\min\{u(g),t\}=t\}$.
--
--   By this lemma, every guarantee of a fraction of the TPS implies the same fraction of the MMS.
--
--   Differences from the source:
--   - generalization: MMS_i ≤ TPS_i ≤ v_i(M)/n → also: the maximum in (2) exists and equals `tps n u`; reason: the first sentence of the page's proof establishes it, and it ties the published `tps` to Definition 2.4; the conclusion of the source is unchanged
--   - encoding: n agents; max in (2) → `0 < n`; `tps` is the `sSup` of the published set without t ≥ 0; reason: the two suprema coincide; Lemma 2.5 here states the maximum
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 2.5, eq. (3), p.8; Definition 2.4, eq. (2), p.7

import Mathlib
import Definitions.Def_TIEMaximin_Shares

namespace TIEMaximin

/-- **Lemma 2.5** (p.8). For every agent, `MMS_i ≤ TPS_i ≤ v_i(M)/n` (3); and the maximum in (2)
exists, as the first sentence of the proof establishes.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 2.5, eq. (3), and Definition 2.4,
eq. (2), pp.7–8.

**Formalization Note.** `0 < n`. The existence of the maximum is stated as: `tps n u` is the
greatest element of the paper's set `{t ≥ 0 : (1/n) Σ_g min{u(g), t} = t}`. This ties `tps`, which
is an `sSup` of the published set without `t ≥ 0`, to Definition 2.4. -/
theorem lemma_2_5 {n m : ℕ} (hn : 0 < n) (u : Fin m → ℝ) (hu : ∀ g, 0 ≤ u g) :
    mmsOf n u ≤ tps n u ∧ tps n u ≤ (∑ g, u g) / (n : ℝ) ∧
    IsGreatest {t : ℝ | 0 ≤ t ∧ 1 / (n : ℝ) * ∑ g, min (u g) t = t} (tps n u) := by sorry

end TIEMaximin
