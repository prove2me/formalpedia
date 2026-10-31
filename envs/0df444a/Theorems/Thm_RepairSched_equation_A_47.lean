-- Prove2me | Theorems.Thm_RepairSched_equation_A_47
-- name    : RepairSched.equation_A_47
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:47.703161+00:00
-- url     : https://prove2.me/theorems/0806a04d-fee4-43fd-bf8a-1e25a7e6c38b
-- title:
--   (A.45)–(A.47), OA pp.32–33 — linear growth of $\mathbf E[W(t)]$ makes the objective infinite
-- statement:
--   If $(W,I,E,a,S)$ is feasible for the EWF (10) and
--   $$\liminf_{t\to\infty}\frac{\mathbf E[W(t)]}{t}>0,$$
--   then the objective value (10a) is $+\infty$.
--
--   This disposes of solutions whose workload grows linearly in the lower bound of Theorem 2.
--
--   Differences from the source:
--   - generalization: liminf E[W(t)]/t = ε for some ε > 0 → liminf E[W(t)]/t > 0, possibly +∞; reason: a positive real ε is one case; the proof covers +∞ too
--   - reading: (10f): a(·,W(·)) is 𝔽-adapted → progressive measurability, and integrable paths (aᵢ − Sᵢ)⁺ on every [0,t]; reason: the paper integrates these paths in (10a)–(10b) and applies Tonelli in (A.47), which needs both
--   - encoding: a(t,W(t,ω),ω) → one process a t ω; reason: the allocation is used only along the path
--   - encoding: real-valued expectations in (10a) → ℝ≥0∞ with lower integrals; reason: the integrands are nonnegative and an infinite expectation stays infinite
--   - encoding: SKU set {1,…,I}, indices j, k → Fin n with n ≥ 1; bjμj/λj and ckμk as minima; reason: only the values of the minima enter the statements
--   - generalization: X is a BM(0,Σ) (p.15) → X arbitrary (no hypothesis on X); reason: the argument (A.45)–(A.47) uses only (10d), (10e) and Tonelli, never the law of X; a BM(0,Σ) is one such X
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (A.45)–(A.47), OA pp.32–33

import Mathlib
import Definitions.Def_RepairSched_Model_IsFeasible
import Definitions.Def_RepairSched_Model_objective

open MeasureTheory Filter

namespace RepairSched

/-- **(A.45)–(A.47): linear growth of the mean workload makes the objective infinite.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), (A.45)–(A.47), OA pp.32–33 (PDF pp.72–73).

If `(W, I, E, a, S)` is feasible for the EWF (10) and `liminf_{t→∞} E[W(t)]/t > 0`, then the
objective (10a) is `+∞`.

**Formalization Note.** The paper supposes that the `liminf` equals some `ε > 0`; here it may
also be `+∞`, since `E[W(t)]` is computed in `ℝ≥0∞`. -/
theorem equation_A_47 {n : ℕ} [NeZero n] (M : Model n) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝔽 : Filtration ℝ mΩ) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → Ω → ℝ)
    (S : Fin n → ℝ) (W I E : ℝ → Ω → ℝ) (a : ℝ → Ω → Fin n → ℝ)
    (hfeas : M.IsFeasible 𝔽 X S W I E a)
    (hlim : 0 < liminf (fun t : ℝ => (∫⁻ ω, ENNReal.ofReal (W t ω) ∂P) / ENNReal.ofReal t) atTop) :
    M.objective P S E a = ⊤ := by sorry

end RepairSched
