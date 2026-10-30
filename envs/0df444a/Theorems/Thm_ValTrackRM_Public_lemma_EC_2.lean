-- Prove2me | Theorems.Thm_ValTrackRM_Public_lemma_EC_2
-- name    : ValTrackRM.Public.lemma_EC_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:27.698185+00:00
-- url     : https://prove2.me/theorems/5611b33c-d359-4805-b818-61dd36b866c8
-- title:
--   Lemma EC.2, p. ec3 — if $j_t>\ell_{i_t,t-1}$, step $t$ earns $\frac1q(r^{(j_t)}-r^{(\ell_{i_t,t-1})})$ in expectation, and $0$ otherwise
-- statement:
--   Consider Algorithm 1 with $k\ge1$ units, price grid $0=r^{(0)}<r^{(1)}<\dots<r^{(m)}$, $m\ge1$, any minimal-level tie-break in line 4, and $q=\sum_{j=1}^m q^{(j)}$ as in Definition 1. Fix a valuation sequence $V_1,\dots,V_T$ and a time step $t\in[T]$. Let $i_t$ be the unit assigned to customer $t$, $\ell=\ell_{i_t,t-1}$ its level before the step, and $j_t$ the index with $V_t=r^{(j_t)}$. Then:
--
--   1. if $j_t>\ell$, the expected revenue of step $t$ is
--   $$
--   \mathbb E[P_tX_t]=\frac1q\bigl(r^{(j_t)}-r^{(\ell)}\bigr);
--   $$
--   2. if $j_t\le\ell$, then $\mathbb E[P_tX_t]=0$.
--
--   Part 1 is Lemma EC.2; part 2 is the observation stated just before it ("there cannot be a sale in a time step $t$ where $j_t\le\ell_{i_t,t-1}$"). Together they say the algorithm earns, in each step, exactly $1/q$ times the increase of the tracked level.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, pp. ec2–ec3, Lemma EC.2 and the preceding remark

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

namespace ValTrackRM.Public

theorem lemma_EC_2 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ V.length) :
    (((levels sel (V.take (t - 1)) (assigned sel V t) : ℕ) < (valIdx V t : ℕ)) →
      stepRevenue r sel V t =
        (1 / qSum r m) * (r (valIdx V t) - r (levels sel (V.take (t - 1)) (assigned sel V t)))) ∧
    (((valIdx V t : ℕ) ≤ (levels sel (V.take (t - 1)) (assigned sel V t) : ℕ)) →
      stepRevenue r sel V t = 0) := by sorry

end ValTrackRM.Public
