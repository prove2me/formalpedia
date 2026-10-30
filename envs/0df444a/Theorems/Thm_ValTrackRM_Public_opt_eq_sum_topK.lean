-- Prove2me | Theorems.Thm_ValTrackRM_Public_opt_eq_sum_topK
-- name    : ValTrackRM.Public.opt_eq_sum_topK
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:30.866987+00:00
-- url     : https://prove2.me/theorems/8b290881-0673-40c9-8a1c-0871df05c2bf
-- title:
--   p. ec4 — OPT $=\sum_{i=1}^k M^k_i(T)$, the sum of the $k$ largest valuations padded with zeros
-- statement:
--   Let $0=r^{(0)}<r^{(1)}<\dots<r^{(m)}$, $m\ge1$, be the price grid, $k\ge1$ the inventory, and $V_1,\dots,V_T$ a valuation sequence with each $V_t\in\{r^{(0)},\dots,r^{(m)}\}$. Let $\mathrm{OPT}$ be the offline optimum, the largest total valuation of a set of at most $k$ customers, and let $M^k(T)$ be the vector of the $k$ largest elements of $(V_1,\dots,V_T)$, filled with zeros if $T<k$ (Definition EC.2). Then
--
--   $$
--   \mathrm{OPT}=\sum_{i=1}^k M^k_i(T).
--   $$
--
--   This identifies the offline benchmark with the vector that the levels of Algorithm 1 track (Lemma EC.4).
--
--   **Formalization Note.** The algorithm parameters (selector) appear only to share the standing hypotheses with the other statements; the identity concerns OPT and $M^k(T)$ alone.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. ec4, Definition EC.2 and the display following it

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

namespace ValTrackRM.Public

theorem opt_eq_sum_topK {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) :
    opt r k V = (topK r k V).sum := by sorry

end ValTrackRM.Public
