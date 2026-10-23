-- Prove2me | Theorems.Thm_ValTrackRM_Public_lemma_EC_4
-- name    : ValTrackRM.Public.lemma_EC_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:28.2257+00:00
-- url     : https://prove2.me/theorems/ba3278b9-b65d-4c19-9d00-27a17c2b0171
-- title:
--   Lemma EC.4, p. ec4 — the levels $(r^{(\ell_{1,t})},\dots,r^{(\ell_{k,t})})$ are a permutation of $M^k(t)$
-- statement:
--   Consider Algorithm 1 with $k\ge1$ units, price grid $0=r^{(0)}<r^{(1)}<\dots<r^{(m)}$, $m\ge1$, and any tie-break in line 4 that assigns each customer to a unit of minimal level. Fix a valuation sequence $V_1,\dots,V_T$. For all $t=0,\dots,T$, the entries of
--
--   $$
--   \bigl(r^{(\ell_{1,t})},\dots,r^{(\ell_{k,t})}\bigr)
--   $$
--
--   are a permutation of the entries of $M^k(t)$, the $k$ largest elements of $(V_1,\dots,V_t)$ padded with zeros (Definition EC.2).
--
--   The levels of the valuation tracking procedure therefore record exactly the $k$ largest valuations seen so far; this is a purely combinatorial statement, with no probability.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. ec4, Lemma EC.4

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

namespace ValTrackRM.Public

theorem lemma_EC_4 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht : t ≤ V.length) :
    (List.ofFn fun i => r (levels sel (V.take t) i)).Perm (topK r k (V.take t)) := by sorry

end ValTrackRM.Public
