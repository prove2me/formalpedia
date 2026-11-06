-- Prove2me | Theorems.Thm_PolytopeSchedPF_lemma_3_2
-- name    : PolytopeSchedPF.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:48.609389+00:00
-- url     : https://prove2.me/theorems/9f8d3179-8d13-4476-b79a-51436abb9d1d
-- title:
--   Lemma 3.2 — KKT consequences of the Eisenberg–Gale program
-- statement:
--   Let $w>0$, let $S\subseteq J$ and let $y=y(S)$ be the optimal solution of (CP) on $S$.
--
--   1. Every vector $\eta\in\mathbb R^D_{\ge0}$ of optimal Lagrange multipliers for (CP) on $S$, that is, every $\eta\ge0$ with
--   $$
--   \frac{w_j}{y_j}=\sum_{d=1}^DB_{dj}\eta_d\ \ (j\in S),\qquad \eta_d\Big(1-\sum_{j\in S}B_{dj}y_j\Big)=0\ \ (d\in[D]),
--   $$
--   satisfies $\sum_{d=1}^D\eta_d=w(S)$.
--   2. Every $\hat y\in\mathcal P$ satisfies
--   $$
--   \sum_{j\in S}\frac{w_j\hat y_j}{y_j}\le w(S).
--   $$
--   3. In particular, $y_j\ge w_jy^{\max}_j/w(S)$ for every $j\in S$.
--
--   Part 2 is the first-order optimality condition of (CP); it is the inequality the analysis of PF uses at every time.
--
--   Differences from the source:
--   - reading: optimal Lagrange multipliers η(S) for (CP) → η ∈ ℝ^D with η ≥ 0, stationarity (8) on S and complementary slackness (9); reason: p.15: together with primal and dual feasibility these conditions characterize optimality
--   - encoding: y(S), the unique optimal solution of (CP) → any y with IsEGOptimal P w S y (y ∈ P_S, positive on S, maximal among vectors of P positive on S); reason: (CP) has log 0 = −∞ and Lean's log 0 = 0; the optimum is unique, so quantifying over every EG-optimal vector is the paper's y(S)
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Lemma 3.2, p.15 (PDF p.17), with (8) and (9)

import Mathlib
import Definitions.Def_PolytopeSchedPF_ProportionalFairness

namespace PolytopeSchedPF

/-- **Lemma 3.2** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §3.2, p.15) ([IKM18, Lemma 3.3 and Proposition 4.1]).
Let `S ⊆ J` and let `y = y(S)` be the optimal solution of (CP) on `S`.
(i) Every vector `η(S)` of optimal Lagrange multipliers for (CP) on `S` satisfies
`∑_{d=1}^{D} η_d(S) = w(S)`.
(ii) Every `ŷ ∈ P` satisfies `∑_{j∈S} w_j ŷ_j / y_j(S) ≤ w(S)`.
In particular, `y_j(S) ≥ w_j y^max_j / w(S)` for every `j ∈ S`.

**Formalization Note** `y(S)` is any vector with `IsEGOptimal P w S y` (it is unique). The optimal
Lagrange multipliers (reading R10) are the vectors `η ≥ 0` satisfying stationarity (8),
`w_j / y_j(S) = ∑_d B_{dj} η_d(S)` for `j ∈ S`, and complementary slackness (9),
`η_d(S) (1 − ∑_{j∈S} B_{dj} y_j(S)) = 0` for every `d` (p.15). -/
theorem lemma_3_2 {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (S : Finset (Fin n)) (y : Fin n → ℝ) (hy : IsEGOptimal P w S y) :
    (∀ η : Fin D → ℝ, (∀ d, 0 ≤ η d) →
        (∀ j ∈ S, w j / y j = ∑ d, P.B d j * η d) →
        (∀ d, η d * (1 - ∑ j ∈ S, P.B d j * y j) = 0) →
        ∑ d, η d = wsum w S) ∧
    (∀ yhat ∈ P.rates, ∑ j ∈ S, w j * yhat j / y j ≤ wsum w S) ∧
    (∀ j ∈ S, w j * P.yMax j / wsum w S ≤ y j) := by sorry

end PolytopeSchedPF
