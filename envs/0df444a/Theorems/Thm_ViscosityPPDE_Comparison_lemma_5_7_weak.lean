-- Prove2me | Theorems.Thm_ViscosityPPDE_Comparison_lemma_5_7_weak
-- name    : ViscosityPPDE.Comparison.lemma_5_7_weak
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:32:16.819115+00:00
-- url     : https://prove2.me/theorems/c0d17813-32b9-469c-b364-eafb8971add7
-- title:
--   Lemma 5.7 under (5.11) — comparison at time 0 against a bounded piecewise-smooth supersolution
-- statement:
--   Let $P_0$ be the Wiener measure and let Assumption 4.2 hold. Let $u^1$ be a viscosity subsolution of the PPDE (3.1), and let $u^2$ satisfy the weaker condition
--   $$u^2\in\bar C^{1,2}_{P_0}(\Lambda)\text{ bounded and }(\mathcal Lu^2)\ge0,\quad u^2(T,\cdot)\ge u^1(T,\cdot),\quad P_0\text{-a.s.}\qquad(5.11)$$
--   Then
--   $$u^1(0,\mathbf 0)\le u^2(0,\mathbf 0).$$
--
--   This is the form in which the proof of Lemma 5.7 is written ("for future purposes, we shall obtain the contradiction under the following slightly weaker assumptions"), and the form that the Perron argument of Section 6 uses: applied at shifted points it gives $u^1\le\bar u$ and (6.3).
--
--   **Formalization Note** The proof derives the contradiction from $u^2_0 - u^1_0 < 0$ at time $0$, so the conclusion is stated at $(0,\mathbf 0)$. Condition (5.11) is the class $\overline{\mathcal D}$ of the Perron file at $(t,\omega) = (0,\mathbf 0)$ with terminal bound $u^1(T,\cdot)$ (there $\omega\otimes_0\omega' = \omega'$ and $P^0_0 = P_0$); "$(\mathcal Lu^2)\ge 0$" is read for $s\in[0,T)$, as in (6.2).
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, proof of Lemma 5.7, (5.11), pp. 23–24

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Perron
import Definitions.Def_ViscosityPPDE_Comparison_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

theorem lemma_5_7_weak {d : ℕ} {T : ℝ≥0} (P0 : Measure (Omega d T 0))
    (hP0 : IsWiener P0) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (g : Omega d T 0 → ℝ) (L0 : ℝ)
    (h42 : Assumption42 f g L0) (u1 u2 : ℝ≥0 → Omega d T 0 → ℝ)
    (h1 : IsViscSub P0 f u1) (h2 : IsSuperC P0 f 0 (zeroPath d T 0) (fun ω => u1 T ω) u2) :
    u1 0 (zeroPath d T 0) ≤ u2 0 (zeroPath d T 0) := by sorry

end ViscosityPPDE.Comparison
