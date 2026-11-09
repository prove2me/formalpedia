-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_theorem_5_3
-- name    : ProcurementPoA.DeterministicCap.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:40.345314+00:00
-- url     : https://prove2.me/theorems/554dc824-cbf5-4e61-a381-71a0193525f8
-- title:
--   Theorem 5.3 — optimal deterministic phantom cap
-- statement:
--   Let $R\ge1$, $e=\exp(1)$, $\varepsilon=e^{-2}$ and
--
--   $$T^\star=\frac{\sqrt{(e^2-1)^2+4e^2R}-(e^2-1)}2,\qquad A(R)=\frac{1-\varepsilon+\sqrt{(1-\varepsilon)^2+4\varepsilon R}}2.$$
--
--   The price of anarchy takes the supremum over every nonempty finite population, all independent Borel cost laws in $[1,R]$, all no-underbidding mixed Bayes–Nash equilibria, and all admissible measurable tie rules. The exact identity and cap bounds are
--
--   $$1\le T^\star\le R,\qquad \operatorname{PoA}_R(M_{T^\star})=A(R)=1+\varepsilon(T^\star-1)=R/T^\star.$$
--
--   Both cap inequalities are strict when $R>1$. For every $1\le T\le R$ the exact worst-case value is
--
--   $$\operatorname{PoA}_R(M_T)=\max\{1+\varepsilon(T-1),R/T\}.$$
--
--   For every real $T<1$, its value is $R$. In particular $T^\star$ minimizes price of anarchy over every deterministic phantom cap $T\le R$, with sharp constant $1/e$. As the real parameter $R$ tends to positive infinity,
--
--   $$\operatorname{PoA}_R(M_{T^\star})=\frac{\sqrt R}{e}+\frac{1-\varepsilon}{2}+O(R^{-1/2}),\qquad \frac{T^\star}{e\sqrt R}\longrightarrow1.$$
--
--   Precisely, some $K>0$ and $R_0\ge1$ bound the absolute displayed remainder by $K/\sqrt R$ for every real $R\ge R_0$. For every original interval $0<L\le U$ and every real normalized cap $T$, the bundled scaling identity is $\operatorname{PoA}_{[L,U]}(M_{LT})=\operatorname{PoA}_{U/L}(M_T)$. This preserves the source's original positive real intervals. The result is a known mathematical theorem and its exact tightness conclusions are proof obligations, not equilibrium assumptions.
--
--   Differences from the source:
--   - generalization: positive nondegenerate cost intervals and scaling for admissible phantom caps → normalized R ≥ 1 and original 0 < L ≤ U, including equal endpoints, with scaling for every real normalized cap T; reason: equal endpoints preserve the nondegenerate claim; positive rescaling of the explicitly defined deterministic rule also covers caps above U, and specializes to every admissible source cap
--   - encoding: Theorem 5.3 gives the cap and asymptotic expansion; Appendix A.1.2 derives exact cap ratios and their minimization → one bundled theorem also states the exact radical identity, all-cap maximum formula, T < 1 case, cap admissibility, optimality and positive scaling; reason: retains the full mathematical conclusions of the selected proof, including sharpness and the complete deterministic phantom class
--   - encoding: O(R^{-1/2}) and T⋆ ≈ e√R → existential positive uniform remainder constant and real threshold, and T⋆/(e√R) tending to 1 as real R tends to +∞; reason: makes the informal asymptotic notation precise without a free error term or restriction to integer R
--   - encoding: worst-case ratio of finite expected costs over instances, mixed equilibria and ties → nonnegative extended-real supremum, exact equality to the finite radical, and its real value in the asymptotic formula; reason: preserves every Borel-law mixed-strategy instance and avoids unbounded real-supremum defaults; exact equality establishes finiteness before real conversion
--   - encoding: independent private costs, mixed used bids and arbitrary tie rules → Fin (n+1) suppliers, measurable possible-type domains with concentrated Borel laws, Markov bid and bid-only tie kernels, and best responses at every declared type for almost every drawn bid against all real deviations; reason: covers every nonempty finite population and cost atoms; the almost-everywhere convention concerns used random bids rather than topological-support endpoints, while incentives remain typewise
-- source:
--   Simone Palazzotto, Andrés Cristi, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Theorem 5.3, printed p. 9 (PDF p. 11); Appendix A.1.2, printed p. 17 (PDF p. 19); scaling printed p. 8 (PDF p. 10); tightness Remark 4.2, printed p. 7 (PDF p. 9)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Efficiency
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open Filter Topology

namespace ProcurementPoA.DeterministicCap

/-- Theorem 5.3 with the exact value and minimization of Appendix A.1.2.
R = 1 is included. Asymptotics use a continuous real parameter at +∞.
The nonnegative extended-real PoA is proved finite by the exact identities
before its real value is used in the remainder formula. -/
theorem theorem_5_3 :
    (∀ R : ℝ, 1 ≤ R →
      1 ≤ capStar R ∧ capStar R ≤ R ∧
      (1 < R → 1 < capStar R ∧ capStar R < R) ∧
      poa R (capStar R) = ENNReal.ofReal (capBound R) ∧
      capBound R = 1 + epsilon * (capStar R - 1) ∧
      capBound R = R / capStar R ∧
      (∀ T : ℝ, 1 ≤ T → T ≤ R →
        poa R T = ENNReal.ofReal (max (1 + epsilon * (T - 1)) (R / T))) ∧
      (∀ T : ℝ, T < 1 → poa R T = ENNReal.ofReal R) ∧
      (∀ T : ℝ, T ≤ R → poa R (capStar R) ≤ poa R T)) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      |(poa R (capStar R)).toReal - Real.sqrt R / Real.exp 1 - (1 - epsilon) / 2|
        ≤ K / Real.sqrt R) ∧
    Tendsto (fun R : ℝ => capStar R / (Real.exp 1 * Real.sqrt R)) atTop (𝓝 1) ∧
    (∀ L U : ℝ, 0 < L → L ≤ U → ∀ T : ℝ,
      poaOn L U (L * T) = poa (U / L) T) := by sorry

end ProcurementPoA.DeterministicCap
