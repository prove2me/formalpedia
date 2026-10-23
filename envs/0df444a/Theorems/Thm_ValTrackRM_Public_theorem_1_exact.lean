-- Prove2me | Theorems.Thm_ValTrackRM_Public_theorem_1_exact
-- name    : ValTrackRM.Public.theorem_1_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:33.961029+00:00
-- url     : https://prove2.me/theorems/6c996b21-c355-4f0c-a383-f68fc134ac0d
-- title:
--   Proof of Theorem 1, p. ec5 — OPT $=\sum_{i=1}^k r^{(\ell_{i,T})}=q\cdot\mathbb E[\mathsf{ALG}]$
-- statement:
--   Consider Algorithm 1 with $k\ge1$ units, price grid $0=r^{(0)}<r^{(1)}<\dots<r^{(m)}$, $m\ge1$, any minimal-level tie-break in line 4, and $q=\sum_{j=1}^m q^{(j)}$ (Definition 1). For every valuation sequence $V_1,\dots,V_T$,
--
--   $$
--   \mathrm{OPT}(V_1,\dots,V_T)=\sum_{i=1}^k r^{(\ell_{i,T})}=q\cdot\mathbb E[\mathsf{ALG}(V_1,\dots,V_T)],
--   $$
--
--   where $\ell_{i,T}$ are the final levels of Algorithm 1, $\mathrm{OPT}$ is the offline optimum and $\mathbb E[\mathsf{ALG}]=\sum_{t=1}^T\mathbb E[P_tX_t]$ is the expected revenue.
--
--   This is the closing display of the proof of Theorem 1: the algorithm earns exactly a $1/q$ fraction of the offline optimum on every sequence, which gives Theorem 1 with equality.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. ec5, proof of Theorem 1

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

namespace ValTrackRM.Public

theorem theorem_1_exact {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) :
    opt r k V = ∑ i, r (levels sel V i) ∧
      ∑ i, r (levels sel V i) = qSum r m * expRevenue r sel V := by sorry

end ValTrackRM.Public
