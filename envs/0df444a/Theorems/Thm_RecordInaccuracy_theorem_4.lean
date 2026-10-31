-- Prove2me | Theorems.Thm_RecordInaccuracy_theorem_4
-- name    : RecordInaccuracy.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:49.518225+00:00
-- url     : https://prove2.me/theorems/67f82c45-8069-4a47-8dfc-96958b9d5a8d
-- title:
--   Theorem 4 — $v_u(F_{Q_0};\tau)$ is unimodal in the restocking time $\tau$ (corrected: needs $\lambda_L+\alpha\lambda_D>0$)
-- statement:
--   Assume the standing parameter assumptions and the feasibility conditions (FC1) and (FC2) of Appendix B. Assume also
--   $$\lambda_{\hat L}=\lambda_L+\alpha\lambda_D>0 .$$
--   Let $v^*_u$ be the bounded measurable value function of problem (4), with $u=v^*_u(\mathbb 1_{\{q=q_m\}})$, and let
--   $$v_u(F;\tau)=\int_0^\tau e^{-\rho s}S^F(s)\Big[c(\Pi^F(s))+h(\Pi^F(s))\,v^*_u\big(J(\Pi^F(s))\big)\Big]ds+(k_R+u)e^{-\rho\tau}S^F(\tau)$$
--   be the objective of (4). Then for every distribution $F=F_{Q_0}$ of the initial shelf stock there exists $\tau^*_u(F)\ge 0$ such that
--
--   1. $\tau\mapsto v_u(F;\tau)$ is strictly decreasing on $[0,\tau^*_u(F)]$, and
--   2. $\tau\mapsto v_u(F;\tau)$ is strictly increasing on $[\tau^*_u(F),\infty)$.
--
--   Hence the optimal restocking policy is a threshold policy: after the $j$-th observable event, restock once the time since that event reaches $\tau^*_u(\Pi(\iota_j))$.
--
--   **Formalization Note** $v_u(F;\tau)$ is `P.objective u V F τ`, with $V$ any bounded measurable solution of (4).
--
--   Differences from the source:
--   - correction: no condition on the rates → $\lambda_L+\alpha\lambda_D>0$; reason: the printed theorem is false otherwise. Take $q_m=1$, $\lambda_D=\rho=k_R=m=1$, $c_D=2$, $\alpha=\lambda_L=\lambda_P=c=c_L=\Delta p=0$ and $F=\mathbb 1_{\{q=1\}}$. Every assumption holds, including (FC1) $0<3$ and (FC2) $2<3$, with $u=1$. Then $v_u(F;\tau)=1+e^{-2\tau}$ is strictly decreasing on all of $[0,\infty)$, so no $\tau^*\ge0$ exists. The proof's Step 2 (p.42), "$\pi_0$ arbitrarily close to 1", needs $\lambda_{\hat L}>0$
--   - reading: $v^*_u$ defined by (SP') and characterized by (4), $u=v^*_u(\mathbb 1_{\{q=q_m\}})$ → any bounded measurable $V$ solving (4) on the simplex, with $u=V(\mathbb 1_{\{q=q_m\}})$; reason: (4) is a contraction on bounded functions, so its bounded solution is unique and equals $v^*_u$
--   - reading: Poisson intensities and probability → $\lambda_D>0$, $\lambda_L,\lambda_P\ge 0$, $\alpha\in[0,1]$ in `Standing`; reason: these are the meanings §2 gives the parameters
--   - encoding: expectation over the next event $\iota$ in (4) → integral against its survival function $S^F$ and hazard $h$; $\tau\in\mathbb R_+$ → $\tau\in[0,\infty)$; flow (1) → normalized matrix exponential; reason: the same quantities written out
-- source:
--   Chehrazi, Inventory Systems with Record Inaccuracy, MSOM (2025), doi:10.1287/msom.2023.0274, Theorem 4, p.17; problem (4), p.16; feasibility conditions, Appendix B, pp.47–48

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders
import Definitions.Def_RecordInaccuracy_Model
import Definitions.Def_RecordInaccuracy_Objective

namespace RecordInaccuracy

/-- **Theorem 4** (Unimodality of `v_u(F_{Q₀}; τ)`), Chehrazi, MSOM (2025),
doi:10.1287/msom.2023.0274, p.17, **corrected**: if `λ_L + αλ_D > 0`, then for every shelf
inventory distribution `F` there is `τ*_u(F) ≥ 0` such that `v_u(F; τ)` is strictly decreasing on
`[0, τ*_u(F)]` and strictly increasing on `[τ*_u(F), ∞)`.

**Formalization Note.** `v_u(F; τ)` is `P.objective u V F τ`, the objective of (4) with
`v*_u = V`, `P.IsValueFunction u V`, `u = V(1{q = q_m})`, and the feasibility conditions FC1, FC2
of Appendix B. The added hypothesis `0 < λ_L̂ = λ_L + αλ_D` corrects the printed theorem: with
`q_m = 1`, `λ_D = ρ = k_R = m = 1`, `c_D = 2`, `α = λ_L = λ_P = c = c_L = Δp = 0` and
`F = 1{q = 1}`, every assumption holds with `u = 1` and `v_u(F; τ) = 1 + e^{−2τ}` decreases
strictly on all of `[0, ∞)`. -/
theorem theorem_4 (P : Params) (hP : P.Standing) (hFC1 : P.FC1)
    (hLhat : 0 < P.lamLhat)
    {u : ℝ} {V : (Fin (P.qm + 1) → ℝ) → ℝ} (hV : P.IsValueFunction u V)
    (hu : u = V P.fullShelf) (hFC2 : P.FC2 u)
    (F : Fin (P.qm + 1) → ℝ) (hF : F ∈ stdSimplex ℝ (Fin (P.qm + 1))) :
    ∃ τstar : ℝ, 0 ≤ τstar ∧
      StrictAntiOn (P.objective u V F) (Set.Icc 0 τstar) ∧
      StrictMonoOn (P.objective u V F) (Set.Ici τstar) := by sorry

end RecordInaccuracy
