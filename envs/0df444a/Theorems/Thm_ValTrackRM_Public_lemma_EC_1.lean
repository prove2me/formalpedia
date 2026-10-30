-- Prove2me | Theorems.Thm_ValTrackRM_Public_lemma_EC_1
-- name    : ValTrackRM.Public.lemma_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:37.641328+00:00
-- url     : https://prove2.me/theorems/ee0f9940-17fa-433c-b14f-20e561f7313c
-- title:
--   Lemma EC.1, p. ec2 — after step $t$, unit $i$ is sold with probability $\frac1q\sum_{j\le\ell_{i,t}}q^{(j)}$
-- statement:
--   Consider Algorithm 1 with $k\ge1$ units, price grid $0=r^{(0)}<r^{(1)}<\dots<r^{(m)}$, $m\ge1$, and any minimal-level tie-break in line 4. Let $q^{(j)}=1-r^{(j-1)}/r^{(j)}$ and $q=\sum_{j=1}^m q^{(j)}$ (Definition 1). Fix a valuation sequence $V_1,\dots,V_T$, let $S_{i,t}$ indicate that unit $i$ is sold by the end of time $t$, and let $\ell_{i,t}$ be the level of unit $i$ at the end of time $t$. Then for all $t=0,\dots,T$ and $i\in[k]$,
--
--   $$
--   \mathbb E[S_{i,t}]=\frac1q\sum_{j=1}^{\ell_{i,t}}q^{(j)} .
--   $$
--
--   This is the invariant that drives the analysis: the probability that a unit has been sold tracks the highest valuation it has been assigned, exactly as in the booking-limit policy of Ball and Queyranne.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. ec2, Lemma EC.1, Equation (EC.3)

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

namespace ValTrackRM.Public

theorem lemma_EC_1 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht : t ≤ V.length) (i : Fin k) :
    probSold r sel (V.take t) i =
      (1 / qSum r m) * ∑ j ∈ Finset.Icc 1 (levels sel (V.take t) i : ℕ), qj r j := by sorry

end ValTrackRM.Public
