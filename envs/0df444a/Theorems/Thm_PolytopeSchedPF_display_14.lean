-- Prove2me | Theorems.Thm_PolytopeSchedPF_display_14
-- name    : PolytopeSchedPF.display_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:19:42.223814+00:00
-- url     : https://prove2.me/theorems/76041999-cc6b-4318-8a41-1bf42cedb9d0
-- title:
--   Display (14) — $\sum_jw_jC_j=\int_0^\infty w(U(t))\,dt$ and $\langle\alpha,p\rangle\le\int_0^\infty H_\alpha(U(t))\,dt$
-- statement:
--   Let $w>0$ and $p\in\mathbb R^n_{\ge0}$, all jobs released at time $0$, and let $y$ be a feasible schedule for $p$ in which the rate of every job is zero from its completion time on. Write $U(t)$ for its unfinished sets. Then
--
--   1. $y(t)\in\mathcal P_{U(t)}$ for every $t\ge0$;
--   2. every job receives exactly $p_j$ units of processing: $\int_0^\infty y_j(t)\,dt=p_j$;
--   3. $\displaystyle\sum_{j\in J}w_jC_j=\int_0^\infty w(U(t))\,dt$;
--   4. for every $\alpha\in\mathbb R^n_{\ge0}$,
--   $$
--   \langle\alpha,p\rangle=\int_0^\infty\langle\alpha,y(t)\rangle\,dt\le\int_0^\infty H_\alpha(U(t))\,dt ,
--   $$
--
--   where every integrand is integrable on $(0,\infty)$.
--
--   These relations compare weighted completion times with linear functions of $p$; Lemmas 5.2 and 5.5 apply them with $H_\alpha(U(t))\le w(U(t))$ and with $\langle\alpha,y(t)\rangle\ge w(U(t))$.
--
--   Differences from the source:
--   - reading: "Since the rate of every job is zero after its completion" → hypothesis hnorm: y_j(t) = 0 for every t ≥ C_j; reason: the paper's standing normalization (p.13: without loss of generality y_j(t) = 0 for t ∉ [r_j, C_j)); display (14) is false for schedules that keep processing completed jobs
--   - encoding: ∫_0^∞ → Lebesgue integral over (0, ∞), with the integrability of every integrand part of the conclusion; reason: Lean's integral is 0 for a non-integrable function
--   - encoding: y(t) ∈ P_{U(t)} for every time t → for every t ≥ 0; reason: schedules are defined on ℝ≥0
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §5.1, p.25 (PDF p.27), display (14) and the sentences before it

import Mathlib
import Definitions.Def_PolytopeSchedPF_Schedule

namespace PolytopeSchedPF

open MeasureTheory

/-- **Display (14)** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.1, p.25). Consider a feasible schedule for `p` with rate vectors
`y(t)` and sets `U(t)` of unfinished jobs. Since the rate of every job is zero after its
completion, `y(t) ∈ P_{U(t)}` for every time `t`, and every job `j` receives exactly `p_j` units
of processing, `∫_0^∞ y(t) dt = p`. Hence, for every `α ∈ ℝⁿ_{≥0}`,
`∑_j w_j C_j = ∫_0^∞ w(U(t)) dt` and `⟨α, p⟩ = ∫_0^∞ ⟨α, y(t)⟩ dt ≤ ∫_0^∞ H_α(U(t)) dt`.

**Formalization Note** Release dates are `0` (§5). The hypothesis `hnorm` is the paper's standing
normalization (p.13: rates vanish from the completion time on; reading R8). `∫_0^∞` is the
Lebesgue integral over `(0, ∞)`, and the integrability of each integrand is part of the
conclusion. -/
theorem display_14 {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (y : ℝ → Fin n → ℝ) (hy : IsFeasible P p 0 y)
    (hnorm : ∀ j (t : ℝ), completionTime p 0 y j ≤ t → y t j = 0) :
    (∀ t : ℝ, 0 ≤ t → y t ∈ P.restricted (unfinished p 0 y t)) ∧
    (∀ j, IntegrableOn (fun t => y t j) (Set.Ioi 0) ∧ ∫ t in Set.Ioi (0 : ℝ), y t j = p j) ∧
    IntegrableOn (fun t => wsum w (unfinished p 0 y t)) (Set.Ioi 0) ∧
    weightedCompletion w p 0 y = ∫ t in Set.Ioi (0 : ℝ), wsum w (unfinished p 0 y t) ∧
    ∀ α : Fin n → ℝ, (∀ j, 0 ≤ α j) →
      IntegrableOn (fun t => dot α (y t)) (Set.Ioi 0) ∧
      IntegrableOn (fun t => P.H α (unfinished p 0 y t)) (Set.Ioi 0) ∧
      dot α p = ∫ t in Set.Ioi (0 : ℝ), dot α (y t) ∧
      ∫ t in Set.Ioi (0 : ℝ), dot α (y t) ≤ ∫ t in Set.Ioi (0 : ℝ), P.H α (unfinished p 0 y t) := by sorry

end PolytopeSchedPF
