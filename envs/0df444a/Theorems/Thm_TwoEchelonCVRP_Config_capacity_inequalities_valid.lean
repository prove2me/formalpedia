-- Prove2me | Theorems.Thm_TwoEchelonCVRP_Config_capacity_inequalities_valid
-- name    : TwoEchelonCVRP.Config.capacity_inequalities_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:26.643198+00:00
-- url     : https://prove2.me/theorems/15d5e904-b677-41cc-b534-68e0ed8f16f2
-- title:
--   §5.2.2 (a) — the capacity constraints (33) are valid for F(M)
-- statement:
--   Let $M$ be a set of first-level routes and let $x$ (with deliveries $q$) be a feasible solution of $F(M)$. For every set $H\subseteq N_C$ of at least two customers,
--   $$\sum_{k\in N_S(M)}\ \sum_{l\in\mathcal R_k:\ R_{kl}\cap H\neq\emptyset}x_{kl}\ \ge\ \Bigl\lceil\frac{\sum_{i\in H}q_i}{Q_2}\Bigr\rceil .$$
--
--   These are the capacity constraints (33) with which the LP relaxation $\bar F(M)$ of $F(M)$ is strengthened; the statement is that they cut off no feasible solution of $F(M)$.
--
--   **Formalization Note** The ceiling is the natural-number ceiling of the rational number $\sum_{i\in H}q_i/Q_2$ (with $Q_2>0$).
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 306, §5.2.2 (a), inequalities (33)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Configuration

namespace TwoEchelonCVRP.Config

/-- §5.2.2 (a), p. 306: the capacity constraints (33) are valid for F(M). For every feasible F(M)
solution and every set `H ⊆ N_C` with `|H| ≥ 2`,
`∑_{k ∈ N_S(M)} ∑_{l ∈ 𝓡_k : R_{kl} ∩ H ≠ ∅} x_{kl} ≥ ⌈∑_{i ∈ H} q_i / Q_2⌉`. -/
theorem capacity_inequalities_valid (I : Instance) (RS : RouteSystem I) (M : Finset RS.FR)
    (t : SolFM RS) (ht : IsFeasibleFM RS M t) (H : Finset (Fin I.nc)) (hH : 2 ≤ H.card) :
    ⌈((∑ i ∈ H, I.q i : ℕ) : ℚ) / (I.Q2 : ℚ)⌉₊
      ≤ ∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ NS RS M ∧ (RS.Rcust l ∩ H).Nonempty),
          (t.x l).toNat := by sorry

end TwoEchelonCVRP.Config
