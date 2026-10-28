-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_11
-- name    : PeriodicMAB.Upper.lemma_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:02.158515+00:00
-- url     : https://prove2.me/theorems/bc181218-2f44-49fa-9ee2-e9d78b25c087
-- title:
--   Lemma 11, p. 22 — the oracle's expected regret is $\le C\sqrt{Td\log^2(T)\log(T/d)}$, $C$ independent of $T$, $K$ and the periods
-- statement:
--   Fix the noise parameter $\sigma>0$. There is a constant $C>0$, depending only on $\sigma$, such that the following holds for every number of arms $K\ge1$, horizon $T$, periods $T_1,\dots,T_K$, means $\mu$ and noise $\epsilon$ satisfying: each $\mu_k$ has minimum period $T_k$, Assumption 1, Assumption 2 with parameter $\sigma$, and Assumption 3 with the parameters (7). Run the weak oracle with $n=\lfloor\sqrt{T/K}\rfloor$ and $\delta=8/T$. Then its pseudo-regret $R^{\tilde\pi}_T$ satisfies
--   $$
--   \mathbb E\big[R^{\tilde\pi}_T\big]\le C\sqrt{T\,d\,\log^2(T)\log(T/d)},\qquad d=\sum_{k=1}^KT_k .
--   $$
--
--   This is the regret of the oracle that knows the periods; the proof of Theorem 1 transfers it to the two-stage policy on the event $\Lambda$.
--
--   **Formalization Note** The expectation is an outer expectation: there is an integrable $Z$ with $R^{\tilde\pi}_T\le Z$ pointwise and $\mathbb E[Z]$ below the bound, so no measurability of the regret is presupposed. The constant is chosen after $\sigma$ and before $K$, $T$, the periods, the means and the noise, matching "the Constant is not related to $T$, $K$ or any $T_k$". The page states the lemma "under Assumption 1 and 2"; its proof also uses $n=\lfloor\sqrt{T/K}\rfloor$ (p. 45), $\delta=8T^{-1}$ (p. 46) and Assumption 3 (through Lemma 16), which are standing assumptions of §4 and are stated as hypotheses. Without Assumption 3, $d\ge T$ is possible and the right-hand side can vanish.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 22, Lemma 11 (proof pp. 44–46)

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 11 (p. 22): under Assumptions 1–3, with the parameters (7) and `δ = 8/T`, the oracle's
expected pseudo-regret is at most `C √(T d log²(T) log(T/d))` with a constant `C` depending on
`σ` only (not on `T`, `K` or the periods). The expectation is an outer expectation. -/
theorem lemma_11 (σ : ℝ≥0) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : ℕ) [NeZero K] (T : ℕ) (Tper : Fin K → ℕ) (μ : Fin K → ℕ → ℝ)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ),
        (∀ k, IsMinPeriod (μ k) (Tper k)) → Assumption1 μ T → IsSubGaussianNoise P ε σ →
        Assumption3 T (nPar T K) (gPar (nPar T K)) Tper →
        ∃ Z : Ω → ℝ, Integrable Z P ∧
          (∀ ω, pseudoRegret μ T (oracle μ ε σ (8 / T) T (nPar T K) Tper ω) ≤ Z ω) ∧
          ∫ ω, Z ω ∂P ≤ C * Real.sqrt (T * effArms Tper * Real.log T ^ 2 *
            Real.log (T / effArms Tper)) := by sorry

end PeriodicMAB.Upper
