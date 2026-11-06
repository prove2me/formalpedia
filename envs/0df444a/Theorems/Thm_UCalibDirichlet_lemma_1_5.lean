-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_1_5
-- name    : UCalibDirichlet.lemma_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:36.56234+00:00
-- url     : https://prove2.me/theorems/5a6ef283-2053-44ef-a4e3-1d42294833ce
-- title:
--   Lemma 1.5 — BTPL regret $\le\Lambda_F(\mathbf 1)+V_F(T)$
-- statement:
--   Let $F:\Delta_K\to\mathbb R$ be convex and normalized by (4), and let $T\ge1$. For every count vector $N\in\mathbb N^K$ with $N_1+\dots+N_K=T$ (the possible values of $N_T$), the BTPL regret term of (8) satisfies
--   $$\Lambda_F(\mathbf 1)-\Lambda_F(N+\mathbf 1)+TF(N/T)\le\Lambda_F(\mathbf 1)+V_F(T),\qquad V_F(T)=T\sup_{p\in\Delta_K}\Big\{F(p)-F\Big(\frac{Tp+\mathbf 1}{T+K}\Big)\Big\}.$$
--
--   The bound isolates the cost of Laplace smoothing in the term $V_F(T)$.
--
--   Differences from the source:
--   - reading: F the potential of the paper's standing setting → F convex on Δ_K and normalized by (4) (IsNormalized); reason: from p.3 on the paper treats F as convex and normalized by (4) 'in all subsequent discussions'; the proof uses F ≥ 0 (p.12)
--   - encoding: the BTPL term with the realized N_T, p̂_T = N_T/T → every N : Fin K → ℕ with ∑ N = T, and 1 ≤ T; reason: N_T ranges over exactly these count vectors; p̂_T is undefined at T = 0
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 1.5, display (9), p.4

import Mathlib
import Definitions.Def_UCalibDirichlet_Lam
import Definitions.Def_UCalibDirichlet_VF
import Definitions.Def_UCalibDirichlet_IsNormalized

namespace UCalibDirichlet

/-- **Lemma 1.5 (BTPL regret).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), Lemma 1.5, display (9), p.4: "The BTPL regret term in (8) is at most
`Λ_F(𝟏) + V_F(T)` where `V_F(T) = T sup_{p∈Δ_K} { F(p) − F((Tp + 𝟏)/(T + K)) }`. (9)"

The BTPL regret term of (8) is `Λ_F(𝟏) − Λ_F(N_T + 𝟏) + T F(p̂_T)` with `p̂_T = N_T/T`. The lemma is
stated for every possible count vector `N_T = N ∈ ℕ^K` with `∑_j N_j = T`.

**Formalization Note.** `F` is a convex function on `Δ_K` normalized by (4) (`IsNormalized`), the
paper's standing convention from p.3 on (its proof uses `F ≥ 0`, p.12). `T ≥ 1`. -/
theorem lemma_1_5 {K : ℕ} (F : (Fin K → ℝ) → ℝ) (hF : ConvexOn ℝ (stdSimplex ℝ (Fin K)) F)
    (hnorm : IsNormalized F) (T : ℕ) (hT : 1 ≤ T) (N : Fin K → ℕ) (hN : ∑ j, N j = T) :
    Lam F (fun _ => 1) - Lam F (fun j => (N j : ℝ) + 1) + T * F (fun j => (N j : ℝ) / T) ≤
      Lam F (fun _ => 1) + VF F T := by sorry

end UCalibDirichlet
