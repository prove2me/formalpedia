-- Prove2me | Theorems.Thm_ValTrackRM_Public_lemma_EC_3
-- name    : ValTrackRM.Public.lemma_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:28.636604+00:00
-- url     : https://prove2.me/theorems/604fb8a7-547d-4aa5-847a-fb940bf2008b
-- title:
--   Lemma EC.3, pp. ec3–ec4 — expected revenue up to time $t$ is $\frac1q\sum_{i=1}^k r^{(\ell_{i,t})}$
-- statement:
--   Consider Algorithm 1 with $k\ge1$ units, price grid $0=r^{(0)}<r^{(1)}<\dots<r^{(m)}$, $m\ge1$, any minimal-level tie-break in line 4, and $q$ as in Definition 1. Fix a valuation sequence $V_1,\dots,V_T$. For every $t\in\{0,\dots,T\}$, the expected revenue earned up to time $t$ satisfies
--
--   $$
--   \sum_{t'=1}^{t}\mathbb E[P_{t'}X_{t'}]=\frac1q\sum_{i=1}^k r^{(\ell_{i,t})},
--   $$
--
--   where $\ell_{i,t}$ is the level of unit $i$ at the end of time $t$.
--
--   The revenue of the online algorithm is thus a deterministic function of the levels, which Lemma EC.4 relates to the offline optimum.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, pp. ec3–ec4, Lemma EC.3

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

namespace ValTrackRM.Public

theorem lemma_EC_3 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht : t ≤ V.length) :
    ∑ t' ∈ Finset.Icc 1 t, stepRevenue r sel V t' =
      (1 / qSum r m) * ∑ i, r (levels sel (V.take t) i) := by sorry

end ValTrackRM.Public
