-- Prove2me | Theorems.Thm_ValTrackRM_Public_line8_unreachable
-- name    : ValTrackRM.Public.line8_unreachable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:16.799398+00:00
-- url     : https://prove2.me/theorems/8b48cfc5-4d55-4d74-a934-a1bf35d67e21
-- title:
--   §3.3, p. 13 — Algorithm 1 never reaches line 8 with $\ell_t=m$: a unit at the top level is sold with probability 1
-- statement:
--   Consider Algorithm 1 (the valuation tracking procedure) with $k\ge1$ units, price grid $0=r^{(0)}<r^{(1)}<\dots<r^{(m)}$, $m\ge1$, and any tie-breaking rule in line 4 that selects a unit of minimal level. Fix a valuation sequence $V_1,\dots,V_T$ and a time $t\in\{0,\dots,T\}$. If inventory unit $i$ has level $\ell_{i,t}=m$ at the end of time $t$, then
--
--   $$
--   \Pr[S_{i,t}=1]=1,
--   $$
--
--   that is, unit $i$ has been sold almost surely.
--
--   Consequently Algorithm 1 cannot branch to line 8 when $\ell_t=m$: the unit $i_t^*$ it would offer is already sold. This is the observation on p. 13 that makes the offer distribution of line 8 well defined (its normalizer $\sum_{j=\ell_t+1}^m q^{(j)}$ is positive exactly when $\ell_t<m$).
--
--   **Formalization Note.** The definition of Algorithm 1 treats a step at a unit of level $m$ as a rejection (price $\infty$) so that it is total; this theorem records that the case never matters.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 13, Section 3.3 (remark after Algorithm 1)

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

namespace ValTrackRM.Public

theorem line8_unreachable {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht : t ≤ V.length) (i : Fin k)
    (hi : levels sel (V.take t) i = Fin.last m) :
    probSold r sel (V.take t) i = 1 := by sorry

end ValTrackRM.Public
