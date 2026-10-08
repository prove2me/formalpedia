-- Prove2me | Theorems.Thm_SmithHitAndRun_SymMixing_theorem_2_strongly_mixing
-- name    : SmithHitAndRun.SymMixing.theorem_2_strongly_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:13:11.763617+00:00
-- url     : https://prove2.me/theorems/176ed517-d79f-4b7e-a90e-e80a16e3972d
-- title:
--   Theorem 2 — convergence to uniformity from every starting point
-- statement:
--   Let $V$ be finite nonzero content on $S$ and $P$ a Markov kernel with a jointly measurable symmetric density $f(y\mid x)$ relative to $V$. Suppose $f(y\mid x)>0$ for every pair $x,y\in S$. Write $\lambda=V/V(S)$ and $P^m(x,A)$ for the $m$-step transition probability. Then for every starting point $x\in S$ and every measurable $A\subseteq S$,
--   $$
--   \lim_{m\to\infty}P^m(x,A)=\lambda(A).
--   $$
--   This is the paper's meaning of **strongly mixing**: setwise convergence to the uniform law from each point. It supplies the qualitative convergence target behind the Random Directions Algorithm. **Formalization Note** The abstract measurable space represents the whole region $S$ and $V$ its content; symmetry of $f$ encodes the consequence Smith asserts for symmetric mixing algorithms satisfying Assumption (a). The statement asks for every $x$, and does not assume stationarity, uniqueness, or a convergence bound.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1301, Theorem 2

import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_MarkovIterKernel
import Definitions.Def_SmithHitAndRun_SymMixing_uniformLaw
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel

open MeasureTheory ProbabilityTheory Filter

namespace SmithHitAndRun.SymMixing

/-- Smith (1984), Theorem 2, p. 1301: setwise convergence from every start. -/
theorem theorem_2_strongly_mixing {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ∀ x : α, ∀ A : Set α, MeasurableSet A →
      Tendsto (fun m : ℕ => MarkovChainCLT.iterKernel P m x A)
        atTop (nhds (uniformLaw V A)) := by sorry

end SmithHitAndRun.SymMixing
