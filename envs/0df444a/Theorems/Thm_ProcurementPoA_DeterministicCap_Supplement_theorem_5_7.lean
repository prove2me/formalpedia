-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_theorem_5_7
-- name    : ProcurementPoA.DeterministicCap.Supplement.theorem_5_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T17:40:32.022083+00:00
-- url     : https://prove2.me/theorems/9b920fea-fca8-4200-aa39-84de670d847f
-- title:
--   Theorem 5.7 — Every regular phantom mechanism has PoA(M) ≥ L_all(R) = (1 − χ + √((1 − χ)² + χR))/2 ≥ √R/8 + 15/32, with χ = 1/16, for every R > 1.
-- statement:
--   Let $R>1$, $\chi=1/16$, and let $M$ be a regular phantom mechanism on any measurable public signal space. Its conditional acceptance function is regular or vanishes above $1$ for almost every signal. Then both inequalities hold:
--   $$\operatorname{PoA}(M)\ge L_{\mathrm{all}}(R):=\frac{1-\chi+\sqrt{(1-\chi)^2+\chi R}}2\ge\frac{\sqrt R}{8}+\frac{15}{32}.$$
--   The supremum defining price of anarchy uses every nonempty finite population, all independent Borel cost laws on $[1,R]$, all measurable lowest-bid tie rules, and all mixed mechanism equilibria with no underbidding. Strategy kernels depend jointly measurably on signal and own cost. No density or finite-signal restriction is imposed.
--
--   This is the paper's lower bound for the whole regular phantom-mechanism class, complementary to the retained optimal deterministic-cap goal. The coefficient $1/8$, the additive $15/32$, and the radical expression are all retained exactly.
--
--   Differences from the source:
--   - encoding: a public signal with conditional phantom law and conditional equilibria → a universe-polymorphic measurable signal space, a signal probability law, a phantom Markov kernel, and jointly measurable signal-and-cost strategy kernels; reason: retains the full signal class and conditional equilibrium criterion of Definition 5.1 and §5.2
--   - encoding: the displayed real PoA lower bound → ofReal(Lall(R)) ≤ the nonnegative extended-real supremum, together with the displayed real lower estimate of Lall; reason: bounded positive instance costs give the same ratios and the complete lattice preserves potentially unbounded suprema without defaults
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Theorem 5.7, printed p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Mechanism

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

universe u

/-- Every regular mechanism on any measurable public signal space, with both exact inequalities. -/
theorem theorem_5_7 (R : ℝ) (hR : 1 < R) {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) (hreg : IsRegularMechanism M) :
    ENNReal.ofReal (Lall R) ≤ mechanismPoA M ∧
    Real.sqrt R / 8 + 15 / 32 ≤ Lall R := by sorry

end ProcurementPoA.DeterministicCap.Supplement
