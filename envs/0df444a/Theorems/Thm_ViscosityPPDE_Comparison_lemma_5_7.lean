-- Prove2me | Theorems.Thm_ViscosityPPDE_Comparison_lemma_5_7
-- name    : ViscosityPPDE.Comparison.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:32:24.552118+00:00
-- url     : https://prove2.me/theorems/15ddd84c-7c4e-4999-acdd-d1340da91621
-- title:
--   Lemma 5.7 — partial comparison: if one of $u^1,u^2$ is in $C^{1,2}_b(\Lambda)$, then $u^1\le u^2$
-- statement:
--   Let $P_0$ be the Wiener measure and let Assumption 4.2 hold. Let $u^1$ be a viscosity subsolution and $u^2$ a viscosity supersolution of the PPDE (3.1). If $u^1(T,\cdot)\le u^2(T,\cdot)$ and one of $u^1$ and $u^2$ is in $C^{1,2}_b(\Lambda)$, then
--   $$u^1(t,\omega)\le u^2(t,\omega)\qquad\text{for all }(t,\omega)\in\Lambda.$$
--
--   This partial comparison principle needs neither the terminal function $g$ between $u^1$ and $u^2$ nor the extension $\hat f$ of Assumption 4.4; it is the first step of the proof of the full comparison principle, Theorem 4.6.
--
--   **Formalization Note** "One of $u^1$, $u^2$ is in $C^{1,2}_b(\Lambda)$" is a disjunction of the existence of a $C^{1,2}_b(\hat\Lambda)$ extension of $u^1$ or of $u^2$. The terminal inequality holds for every $\omega$. Assumption 4.2 is the structure on $(f,g)$; $g$ plays no role in the statement, and any $g$ satisfying 4.2(ii) (for instance $g = 0$) may be taken.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, Lemma 5.7, p. 23

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Perron
import Definitions.Def_ViscosityPPDE_Comparison_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

theorem lemma_5_7 {d : ℕ} {T : ℝ≥0} (P0 : Measure (Omega d T 0))
    (hP0 : IsWiener P0) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (g : Omega d T 0 → ℝ) (L0 : ℝ)
    (h42 : Assumption42 f g L0) (u1 u2 : ℝ≥0 → Omega d T 0 → ℝ)
    (h1 : IsViscSub P0 f u1) (h2 : IsViscSuper P0 f u2) (hT : ∀ ω, u1 T ω ≤ u2 T ω)
    (hreg : (∃ X, ExtC12b T 0 u1 X) ∨ (∃ X, ExtC12b T 0 u2 X)) :
    ∀ t ω, t ≤ T → u1 t ω ≤ u2 t ω := by sorry

end ViscosityPPDE.Comparison
