-- Prove2me | Theorems.Thm_RecordInaccuracy_theorem_2
-- name    : RecordInaccuracy.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:51.941682+00:00
-- url     : https://prove2.me/theorems/f77cfd0e-4846-4235-a316-60d918856083
-- title:
--   Theorem 2 — first-order monotonicity: $Q^1_0\le_{st}Q^2_0\Rightarrow v^*_u(F_{Q^1_0})\ge v^*_u(F_{Q^2_0})$
-- statement:
--   Assume the standing parameter assumptions and the feasibility conditions (FC1) and (FC2) of Appendix B. Let $v^*_u$ be the value function of problem (4): bounded and measurable, with
--   $$v^*_u(F)=\inf_{\tau\in\mathbb R_+}v_u(F;\tau)$$
--   for every distribution $F$. Let $u=v^*_u(\mathbb 1_{\{q=q_m\}})$. If $F_{Q^1_0}$ and $F_{Q^2_0}$ are any two distributions of the initial shelf stock with $Q^1_0\le_{st}Q^2_0$, then
--   $$v^*_u(F_{Q^1_0})\ \ge\ v^*_u(F_{Q^2_0}).$$
--
--   The expected minimum cost is higher when the retailer expects less inventory on the shelf. The two distributions need not be reachable from a sequence of observable events.
--
--   **Formalization Note** $Q^1_0\le_{st}Q^2_0$ is `StochGE F₂ F₁` (upper tail sums of $F_2$ dominate, larger argument first).
--
--   Differences from the source:
--   - reading: "$<_{st}$" → the non-strict first-order stochastic order $\le_{st}$ (`StochGE`); reason: the paper uses Shaked–Shanthikumar's orders (footnote 22); a non-strict hypothesis gives the stronger theorem
--   - reading: $v^*_u$ defined by (SP') and characterized by (4), $u=v^*_u(\mathbb 1_{\{q=q_m\}})$ → any bounded measurable $V$ solving (4) on the simplex, with $u=V(\mathbb 1_{\{q=q_m\}})$; reason: (4) is a contraction on bounded functions, so its bounded solution is unique and equals $v^*_u$
--   - reading: Poisson intensities and probability → $\lambda_D>0$, $\lambda_L,\lambda_P\ge 0$, $\alpha\in[0,1]$ in `Standing`; reason: these are the meanings §2 gives the parameters
--   - encoding: expectation over the next event $\iota$ in (4) → integral against its survival function $S^F$ and hazard $h$; "$\inf_{\tau\in\mathbb R_+}$" → `IsGLB` over $\tau\in[0,\infty)$; flow (1) → normalized matrix exponential; reason: the same quantities written out
-- source:
--   Chehrazi, Inventory Systems with Record Inaccuracy, MSOM (2025), doi:10.1287/msom.2023.0274, Theorem 2, p.16 (domain stated on p.17); feasibility conditions, Appendix B, pp.47–48

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders
import Definitions.Def_RecordInaccuracy_Model
import Definitions.Def_RecordInaccuracy_Objective

namespace RecordInaccuracy

open LovejoyPOMDP.Monotone

/-- **Theorem 2** (First-Order Monotonicity), Chehrazi, MSOM (2025), doi:10.1287/msom.2023.0274,
p.16: if `Q¹₀ ≤st Q²₀` then `v*_u(F_{Q¹₀}) ≥ v*_u(F_{Q²₀})`, for any two shelf inventory
distributions (p.17: "regardless of whether the two distributions … can be obtained from a
sequence of observable events").

**Formalization Note.** `v*_u` is any `V` with `P.IsValueFunction u V` (bounded measurable
solution of (4), unique by contraction), and `u = V(1{q = q_m})` (p.13). The feasibility
conditions of Appendix B are hypotheses ("we assume that the above feasibility conditions hold
throughout the text", p.48). `Q¹₀ ≤st Q²₀` is `StochGE F₂ F₁` (larger first). -/
theorem theorem_2 (P : Params) (hP : P.Standing) (hFC1 : P.FC1)
    {u : ℝ} {V : (Fin (P.qm + 1) → ℝ) → ℝ} (hV : P.IsValueFunction u V)
    (hu : u = V P.fullShelf) (hFC2 : P.FC2 u)
    {F₁ F₂ : Fin (P.qm + 1) → ℝ} (hF₁ : F₁ ∈ stdSimplex ℝ (Fin (P.qm + 1)))
    (hF₂ : F₂ ∈ stdSimplex ℝ (Fin (P.qm + 1))) (h12 : StochGE F₂ F₁) :
    V F₂ ≤ V F₁ := by sorry

end RecordInaccuracy
