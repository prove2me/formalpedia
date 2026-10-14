-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_theorem_1
-- name    : PeriodicMAB.Upper.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:51.677979+00:00
-- url     : https://prove2.me/theorems/e4a626e4-5db3-4e3b-aa9d-b88a49653f97
-- title:
--   Theorem 1, pp. 16–17 — $\mathbb E[R^\pi_T]\le C\sqrt{Td\log^2(T)\log(T/d)}$ for the two-stage policy
-- statement:
--   Fix the noise parameter $\sigma>0$ and the number of arms $K\ge1$. There is a constant $C>0$ such that the following holds for every horizon $T$, periods $T_1,\dots,T_K$, means $\mu$ and noise $\epsilon$ satisfying: each $\mu_k$ has minimum period $T_k$, Assumption 1, Assumption 2 with parameter $\sigma$, and Assumptions 3 and 4 with the parameters (7), $n=\lfloor\sqrt{T/K}\rfloor$, $g=\lceil\sqrt n\rceil$, $H=\sqrt{1+\log n}$. Run the two-stage policy $\pi$ of §3 (Algorithm 1, then Algorithm 2 with $\delta=8/T$). Then
--   $$
--   \mathbb E\big[R^\pi_T\big]\le C\sqrt{T\,d\,\log^2(T)\log(T/d)},\qquad d=\sum_{k=1}^KT_k .
--   $$
--
--   The policy learns the unknown periods and then the $d$ effective arms, and its regret matches, up to logarithmic factors, the $\sqrt{TK}$ rate of the stationary bandit with $d$ arms in place of $K$.
--
--   **Formalization Note** The expectation is an outer expectation: there is an integrable $Z$ with $R^\pi_T\le Z$ pointwise and $\mathbb E[Z]$ below the bound. The paper says "the Constant does not depend on $T$, $K$ or any $T_k$". Its proof (p. 22) bounds the stage-one failure term by $T(48K/n^{H^2-1}+200K/n^{0.867H^2-1}+200K/n^{0.694H^2-1})$, which is bounded by a multiple of the main term uniformly in $T$ only for fixed $K$; the statement therefore lets $C$ depend on $\sigma$ and $K$, and chooses it before $T$, the periods, the means and the noise. Theorem 1 fixes the parameters (7) but not Algorithm 2's $\delta$; the statement uses $\delta=8/T$, the value of the proof of Lemma 11 (p. 46). Assumption 3 with (7) forces $n\ge7$, hence $T\ge49K$ and $8/T\in(0,1)$. The algorithms are as defined in `PeriodicMAB.Upper.Spectral` and `PeriodicMAB.Upper.Policy`, with their canonical tie-breaking.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, pp. 16–17, Theorem 1 (proof p. 22)

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Theorem 1 (pp. 16–17): under Assumptions 1–4, with the parameters (7) and `δ = 8/T`, the
two-stage policy's expected pseudo-regret is at most `C √(T d log²(T) log(T/d))`, `d = ∑_k T_k`,
with a constant `C` depending only on `σ` and `K` (chosen before `T`, the periods, the means
and the noise). The expectation is an outer expectation. -/
theorem theorem_1 (σ : ℝ≥0) (hσ : 0 < σ) (K : ℕ) [NeZero K] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℕ) (Tper : Fin K → ℕ) (μ : Fin K → ℕ → ℝ)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ),
        (∀ k, IsMinPeriod (μ k) (Tper k)) → Assumption1 μ T → IsSubGaussianNoise P ε σ →
        Assumption3 T (nPar T K) (gPar (nPar T K)) Tper →
        Assumption4 μ Tper σ (HPar (nPar T K)) (nPar T K) (gPar (nPar T K)) →
        ∃ Z : Ω → ℝ, Integrable Z P ∧
          (∀ ω, pseudoRegret μ T
            (twoStage μ ε σ (8 / T) (HPar (nPar T K)) T (nPar T K) (gPar (nPar T K)) ω) ≤ Z ω) ∧
          ∫ ω, Z ω ∂P ≤ C * Real.sqrt (T * effArms Tper * Real.log T ^ 2 *
            Real.log (T / effArms Tper)) := by sorry

end PeriodicMAB.Upper
