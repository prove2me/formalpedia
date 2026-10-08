-- Prove2me | Theorems.Thm_TsallisINF_Half_theorem_1_rv
-- name    : TsallisINF.Half.theorem_1_rv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:12.260998+00:00
-- url     : https://prove2.me/theorems/64936a5c-cf5c-4899-9f7e-bc1e7c230bf4
-- title:
--   Theorem 1 (RV): adversarial and self-bounding pseudo-regret
-- statement:
--   Run symmetric half-Tsallis-INF with reduced-variance estimates, learning rate $\eta_t=4/\sqrt t$, $K\ge1$ arms, and any randomized adaptive adversary whose losses lie in $[0,1]$. For every horizon $T\ge1$, its pseudo-regret satisfies
--
--   $$
--   \operatorname{Reg}_T\le2\sqrt{KT}+14K\log T+16.
--   $$
--
--   Suppose also that $K\ge2$, $C\ge0$, a gap vector $\Delta\in[0,1]^K$ has a unique zero at $i^*$, and the self-bounding constraint $\operatorname{Reg}_T\ge\mathbb E[\sum_{t=1}^T\sum_{i\ne i^*}w_{t,i}\Delta_i]-C$ holds. Put $\Delta_{\min}=\min_{i\ne i^*}\Delta_i$ and $X=\sum_{i\ne i^*}(\log T+3)/\Delta_i+2/\Delta_{\min}$. Then
--
--   $$
--   \operatorname{Reg}_T\le X+28K\log T+\tfrac32\sqrt K+32+C.
--   $$
--
--   When $C>X$, it also satisfies
--
--   $$
--   \operatorname{Reg}_T\le2\sqrt{XC}+28K\log T+\tfrac32\sqrt K+32.
--   $$
--
--   These are simultaneous guarantees for one algorithm in adversarial and self-bounding regimes.
--
--   **Formalization Note** The printed adversarial display has $10K\log T$, while its proof on p. 21 yields $14K\log T$; the latter is formalized. Section 2 defines the self-bounding regime with $C\ge0$, and the minimum positive gap requires $K\ge2$. The paper's last display says $\operatorname{Reg}_t$ where $\operatorname{Reg}_T$ is intended.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, pp. 9–10, Theorem 1 (RV); p. 21 proof of the adversarial constant

import Mathlib
import Definitions.Def_TsallisINF_Half_Setting

open MeasureTheory

namespace TsallisINF.Half

/-- Theorem 1 for the RV estimator. The adversarial constant follows the proof on page 21. -/
theorem theorem_1_rv {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF etaRV (estRV etaRV adv W) W)
    (T : ℕ) (hT : 1 ≤ T) :
    pseudoRegret μ adv W (⟨0, hK⟩ : Fin K) T ≤
        2 * Real.sqrt ((K : ℝ) * (T : ℝ)) +
          14 * (K : ℝ) * Real.log (T : ℝ) + 16 ∧
      ∀ (Δ : Fin K → ℝ) (istar : Fin K) (C : ℝ),
        1 < K →
        0 ≤ C →
        (∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1) →
        Δ istar = 0 →
        (∀ i, i ≠ istar → 0 < Δ i) →
        SelfBounding μ adv W (⟨0, hK⟩ : Fin K) T Δ istar C →
        let X : ℝ :=
          (∑ i ∈ Finset.univ.erase istar,
            (Real.log (T : ℝ) + 3) / Δ i) + 2 / deltaMin Δ istar
        pseudoRegret μ adv W (⟨0, hK⟩ : Fin K) T ≤
            X + 28 * (K : ℝ) * Real.log (T : ℝ) +
              (3 / 2 : ℝ) * Real.sqrt (K : ℝ) + 32 + C ∧
          (X < C → pseudoRegret μ adv W (⟨0, hK⟩ : Fin K) T ≤
            2 * Real.sqrt (X * C) + 28 * (K : ℝ) * Real.log (T : ℝ) +
              (3 / 2 : ℝ) * Real.sqrt (K : ℝ) + 32) := by sorry

end TsallisINF.Half
