-- Prove2me | Theorems.Thm_ReportDepSP_Honesty_delta_v_nonneg
-- name    : ReportDepSP.Honesty.delta_v_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:58.610547+00:00
-- url     : https://prove2.me/theorems/61b8c925-0408-4c7f-bb4c-070ea891c9a4
-- title:
--   Proof of Proposition 2, p. 12 — ∆_v ≥ 0 for decreasing v
-- statement:
--   Let $P\ge 0$ be a nonnegative weight function on attainability states, $\widetilde R$ any ROL, and $v$ a payoff vector with $v_1 \ge v_2 \ge \dots \ge v_n$. Then the report-independent part of the payoff difference is nonnegative:
--   $$\Delta_v = \sum_{s=1}^n v_s\bigl(f_s - \widetilde f_{\widetilde R(s)}\bigr) \ \ge\ 0 .$$
--
--   Together with the decomposition $U(v\mid R) - U(v\mid\widetilde R) = \Delta_v + \Delta_\rho$, this reduces the comparison of the true list with $\widetilde R$ to the report-dependent part $\Delta_\rho$.
--
--   **Formalization Note** The paper writes "$\Delta_v > 0$". The strict inequality fails in general: if $P$ is a point mass on a state in which exactly one option is attainable, every list is matched with that option and $\Delta_v = 0$. The weak inequality is what the proof of Proposition 2 uses. The decreasing order of $v$ is the paper's standing relabeling (p. 5); options are 0-indexed `Fin n`.
-- source:
--   Meisner, Report-dependent utility and strategy-proofness, CRC TRR 190 Discussion Paper No. 289 (2021; Management Science doi:10.1287/mnsc.2022.4504), proof of Proposition 2 (Appendix), p. 12, "where ∆_v > 0 as strategy-proofness implies a first-order stochastic dominance of the true lottery"

import Mathlib
import Definitions.Def_ReportDepSP_Honesty_Setting

namespace ReportDepSP.Honesty

open Finset

/-- Proof of Proposition 2 (p. 12): `∆_v = Σ_r v_r (f_r − f̃_{R̃(r)}) ≥ 0` for `v` decreasing
(the page prints `∆_v > 0`, which fails in general; the weak inequality is what the proof uses). -/
theorem delta_v_nonneg {n : ℕ} (P : (Fin n → Bool) → ℝ) (Rt : Equiv.Perm (Fin n))
    (hP0 : ∀ a, 0 ≤ P a) (v : Fin n → ℝ) (hv : Antitone v) :
    0 ≤ ∑ s : Fin n, v s * (matchProb P 1 s - matchProb P Rt (Rt s)) := by sorry

end ReportDepSP.Honesty
