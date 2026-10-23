-- Prove2me | Theorems.Thm_ValTrackRM_Public_theorem_1
-- name    : ValTrackRM.Public.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:43.573843+00:00
-- url     : https://prove2.me/theorems/18a908ce-09be-4906-bc81-09d493a68f3d
-- title:
--   Theorem 1, p. 14 — the valuation tracking procedure (Algorithm 1) is $c^*(\mathcal P)$-competitive: $\mathbb E[\mathsf{ALG}]\ge \mathrm{OPT}/q$ on every valuation sequence
-- statement:
--   Let $m\ge1$ and $0<r^{(1)}<\dots<r^{(m)}$ be the price set $\mathcal P$, with $r^{(0)}=0$, and let $k\ge1$ be the starting inventory. Let $q^{(j)}=1-r^{(j-1)}/r^{(j)}$, $q=\sum_{j=1}^m q^{(j)}$ and $c^*(\mathcal P)=1/q$ (Definition 1). Run Algorithm 1, the valuation tracking procedure, with any rule for breaking ties in the arg min of line 4. Then for every valuation sequence $(V_1,\dots,V_T)\in(\mathcal P\cup\{0\})^T$,
--
--   $$
--   \mathbb E[\mathsf{ALG}(V_1,\dots,V_T)]\ \ge\ c^*(\mathcal P)\cdot\mathrm{OPT}(V_1,\dots,V_T),
--   $$
--
--   where $\mathsf{ALG}=\sum_{t=1}^T P_tX_t$ is the revenue of the algorithm and $\mathrm{OPT}$ the offline optimum, the sum of the $\min\{k,T\}$ largest valuations. That is, Algorithm 1 is $c^*(\mathcal P)$-competitive in the sense of Equation (1).
--
--   Since $c^*(\mathcal P)$ is also an upper bound on the competitiveness of any online algorithm (Ball and Queyranne 2009; Eren and Maglaras 2010), Theorem 1 shows that the competitive ratio of public dynamic pricing with deterministic valuations equals $c^*(\mathcal P)$.
--
--   **Formalization Note.** $\mathbb E[\mathsf{ALG}]$ is computed from the law of Algorithm 1's random prices and purchases (the law of the sold vector, pushed forward step by step), and OPT is the offline maximum over sets of at most $k$ customers; neither is defined through the algorithm's levels. The price at step $t$ depends only on $V_1,\dots,V_{t-1}$. The statement holds for every list of valuations, including the empty one (where both sides are $0$), and for every minimal-level tie-break; both are strengthenings of the paper's "for all $T\ge1$" with one fixed arg min. The printed line 8 of Algorithm 1 has a typo in its last probability (`ℓt+1/q_tot`); the definition uses $q^{(m)}/q_{\mathrm{tot}}$.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 14, Theorem 1 (with Equation (1), p. 8, and Definition 1, pp. 8–9)

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

namespace ValTrackRM.Public

theorem theorem_1 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) :
    cStar r m * opt r k V ≤ expRevenue r sel V := by sorry

end ValTrackRM.Public
