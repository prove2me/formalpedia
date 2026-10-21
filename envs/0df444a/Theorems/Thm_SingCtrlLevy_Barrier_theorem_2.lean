-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_theorem_2
-- name    : SingCtrlLevy.Barrier.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:40.627452+00:00
-- url     : https://prove2.me/theorems/c3df2161-623b-459c-8845-31b8213cdf16
-- title:
--   Theorem 2, p. 13 — for a convex running cost and a general Lévy process, the barrier strategy at b* is optimal over all admissible strategies
-- statement:
--   Let $X$ be a real Lévy process with triplet $(\gamma,\sigma,\Pi)$ such that $\int_{\mathbb R\setminus(-1,1)}e^{\bar\theta|z|}\Pi(dz)<\infty$ for some $\bar\theta>0$ (Assumption 2(ii)). Let $q>0$, $C\in\mathbb R$, and let the running cost $f$ be convex with polynomial growth and $f'_+(-\infty)<-Cq<f'_+(\infty)$ (Assumption 1). Let
--   $$b^*=\inf\{b\in\mathbb R:\rho(b)+C\ge0\},\qquad \rho(b)=\mathbb E\Big[\int_0^\infty e^{-qt}f'_+(U^0_t+b)\,dt\Big].$$
--   Then the barrier strategy $\pi^{b^*}$, which reflects $X$ at the lower barrier $b^*$, is optimal over all admissible strategies: for every starting point $x\in\mathbb R$, $\pi^{b^*}$ is admissible from $x$ and
--   $$v_{\pi^{b^*}}(x)\le v_\pi(x)\qquad\text{for every strategy }\pi\text{ admissible from }x ,$$
--   so $v(x)=v_{b^*}(x)$, where
--   $v_\pi(x)=\mathbb E_x\big[\int_0^\infty e^{-qt}f(U^\pi_t)\,dt+C\int_{[0,\infty)}e^{-qt}\,dR^\pi_t\big]$.
--
--   This is the main result of the paper. It covers Lévy processes of bounded and unbounded variation, with jumps of both signs, including subordinators and driftless compound Poisson processes, and the optimal barrier is given by the explicit equation $\rho(b)+C=0$.
--
--   **Formalization Note** No Assumption 2(i) and no Assumption 3 appear: §4.2 removes Assumption 3 and §5 extends the result to driftless compound Poisson processes ("This completes the proof of Theorem 2 when X is a driftless compound Poisson process", p. 23). Optimality is stated without the infimum $v$: admissibility of $\pi^{b^*}$ plus domination of every admissible strategy, at every start. Strategies are adapted to the natural filtration of $X$ and chosen for the given start $x$; the control cost includes the initial jump $R_0$.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 13, Theorem 2 (with §4.2 pp. 17–21 and §5 pp. 21–23 for the general and driftless compound Poisson cases)

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (x : ℝ) :
    IsAdmissible P X f q x (barrierR X x (bstar P X f q C)) ∧
      ∀ R : ℝ≥0 → Ω → ℝ, IsAdmissible P X f q x R →
        cost P X f q C x (barrierR X x (bstar P X f q C)) ≤ cost P X f q C x R := by sorry

end SingCtrlLevy.Barrier
