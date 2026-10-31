-- Prove2me | Theorems.Thm_RecordInaccuracy_theorem_3
-- name    : RecordInaccuracy.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:56.689891+00:00
-- url     : https://prove2.me/theorems/387a5f63-c392-4ac0-8be4-164b082b8412
-- title:
--   Theorem 3 — single crossing of $v_u(F_{Q_0};\tau)$ through $k_R+u$
-- statement:
--   Assume the standing parameter assumptions and the feasibility conditions (FC1) and (FC2). Let $v^*_u$ be the bounded measurable value function of problem (4), with $u=v^*_u(\mathbb 1_{\{q=q_m\}})$, and let $v_u(F;\tau)$ be the objective of (4). Let $Q^1_0\le_{st}Q^2_0$, and let $\tau\ge 0$. If
--   $$v_u(F_{Q^2_0};\tau)>k_R+u,$$
--   then
--   $$v_u(F_{Q^1_0};\tau)>k_R+u.$$
--
--   Here $k_R+u$ is the cost of restocking immediately. If postponing restocking to $\tau$ is worse than restocking now when more stock is expected, it is also worse when less stock is expected.
--
--   **Formalization Note** $v_u(F;\tau)$ is `P.objective u V F τ`; $Q^1_0\le_{st}Q^2_0$ is `StochGE F₂ F₁`.
--
--   Differences from the source:
--   - reading: "$<_{st}$" → the non-strict first-order stochastic order $\le_{st}$ (`StochGE`); reason: the paper uses Shaked–Shanthikumar's orders (footnote 22); a non-strict hypothesis gives the stronger theorem
--   - reading: $v^*_u$ defined by (SP') and characterized by (4), $u=v^*_u(\mathbb 1_{\{q=q_m\}})$ → any bounded measurable $V$ solving (4) on the simplex, with $u=V(\mathbb 1_{\{q=q_m\}})$; reason: (4) is a contraction on bounded functions, so its bounded solution is unique and equals $v^*_u$
--   - reading: Poisson intensities and probability → $\lambda_D>0$, $\lambda_L,\lambda_P\ge 0$, $\alpha\in[0,1]$ in `Standing`; reason: these are the meanings §2 gives the parameters
--   - encoding: expectation over the next event $\iota$ in (4) → integral against its survival function $S^F$ and hazard $h$; $\tau\in\mathbb R_+$ → $\tau\in[0,\infty)$; flow (1) → normalized matrix exponential; reason: the same quantities written out
-- source:
--   Chehrazi, Inventory Systems with Record Inaccuracy, MSOM (2025), doi:10.1287/msom.2023.0274, Theorem 3, p.17; problem (4), p.16; feasibility conditions, Appendix B, pp.47–48

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders
import Definitions.Def_RecordInaccuracy_Model
import Definitions.Def_RecordInaccuracy_Objective

namespace RecordInaccuracy

open LovejoyPOMDP.Monotone

/-- **Theorem 3** (Single-Crossing Property of `v_u(F_{Q₀}; τ)`), Chehrazi, MSOM (2025),
doi:10.1287/msom.2023.0274, p.17: let `Q¹₀ ≤st Q²₀`; if `v_u(F_{Q²₀}; τ) > k_R + u` then
`v_u(F_{Q¹₀}; τ) > k_R + u`.

**Formalization Note.** `v_u(F; τ)` is `P.objective u V F τ`, the objective of (4) with
`v*_u = V`, `P.IsValueFunction u V`, `u = V(1{q = q_m})`, and the feasibility conditions of
Appendix B. Restocking times range over `τ ∈ [0, ∞)`. `Q¹₀ ≤st Q²₀` is `StochGE F₂ F₁`. -/
theorem theorem_3 (P : Params) (hP : P.Standing) (hFC1 : P.FC1)
    {u : ℝ} {V : (Fin (P.qm + 1) → ℝ) → ℝ} (hV : P.IsValueFunction u V)
    (hu : u = V P.fullShelf) (hFC2 : P.FC2 u)
    {F₁ F₂ : Fin (P.qm + 1) → ℝ} (hF₁ : F₁ ∈ stdSimplex ℝ (Fin (P.qm + 1)))
    (hF₂ : F₂ ∈ stdSimplex ℝ (Fin (P.qm + 1))) (h12 : StochGE F₂ F₁)
    {τ : ℝ} (hτ : 0 ≤ τ) (hcross : P.kR + u < P.objective u V F₂ τ) :
    P.kR + u < P.objective u V F₁ τ := by sorry

end RecordInaccuracy
