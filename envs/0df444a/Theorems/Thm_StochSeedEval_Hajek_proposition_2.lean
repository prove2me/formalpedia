-- Prove2me | Theorems.Thm_StochSeedEval_Hajek_proposition_2
-- name    : StochSeedEval.Hajek.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:41.500995+00:00
-- url     : https://prove2.me/theorems/72a71bf2-f3a0-4fa4-8063-1afb5e03eebf
-- title:
--   Proposition 2 — corrected almost-sure consistency and asymptotic normality of the Hájek estimator
-- statement:
--   Consider two strategy distributions $p_A,p_B$ and a design distribution $p_\Delta$ on a countable seed-set space, with fixed real outcome $y(s)$. Let $S_0,S_1,\ldots$ be independent observations with common law $p_\Delta$, and let $\widetilde\tau_N$ be the Hájek estimator (7), calculated from the first $N$ observations and the known probabilities. Suppose $p_\Delta(s)>0$ wherever $p_A(s)>0$ or $p_B(s)>0$, and suppose $w_A$, $w_B$, $w_Ay$, and $w_By$ have finite second moments under $p_\Delta$. Then
--
--   $$\widetilde\tau_N\longrightarrow\tau_{\mathrm{sp}}=\mu_A-\mu_B\quad\text{almost surely},\qquad\sqrt N(\widetilde\tau_N-\tau_{\mathrm{sp}})\Rightarrow\mathcal N(0,V_{\widetilde\tau}),$$
--
--   where $\mu_A=\mathbb E_A[y(S)]$, $\mu_B=\mathbb E_B[y(S)]$, and the variance is exactly equation (15):
--
--   $$V_{\widetilde\tau}=\mathbb E_\Delta\left[\left(\frac{\mu_Ap_A(S)-\mu_Bp_B(S)-y(S)(p_A(S)-p_B(S))}{p_\Delta(S)}\right)^2\right].$$
--
--   This gives the large-sample target and normal limit for a difference of two dependent, self-normalized importance sampling estimates.
--
--   **Formalization Note.** The statement corrects Proposition 2's too-weak Assumption 1 by imposing full positivity and spells out the finite second moments used by its proof. The sample is indexed from zero. The Gaussian target is represented by any random variable with that exact law; its variance is computed from (15), not chosen independently. Lean's total division gives defined finite-sample values even when a normalizing sum vanishes.
-- source:
--   Chin, Eckles & Ugander, Evaluating Stochastic Seeding Strategies in Networks, arXiv:1809.09561v3, p. 14, Proposition 2 and equation (15), proof pp. 39–40 (corrected positivity and moment hypotheses)

import Mathlib
import Definitions.Def_StochSeedEval_Hajek_Estimators

open MeasureTheory ProbabilityTheory Filter Topology

namespace StochSeedEval.Hajek

/-- Corrected Proposition 2, p. 14: almost-sure consistency and asymptotic normality. -/
theorem proposition_2
    {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hA2 : MemLp (weightA pA pD) 2 pD.toMeasure)
    (hB2 : MemLp (weightB pB pD) 2 pD.toMeasure)
    (hAy2 : MemLp (fun s => weightA pA pD s * y s) 2 pD.toMeasure)
    (hBy2 : MemLp (fun s => weightB pB pD s * y s) 2 pD.toMeasure)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure)
    {Ω'' : Type*} [MeasurableSpace Ω''] (Q : Measure Ω'') [IsProbabilityMeasure Q]
    (Z : Ω'' → ℝ)
    (hZ : HasLaw Z (gaussianReal 0 (asymptoticVariance pA pB pD y).toNNReal) Q) :
    (∀ᵐ ω ∂P, Tendsto (fun N => hajek pA pB pD y S N ω) atTop (𝓝 (contrast pA pB y))) ∧
    TendstoInDistribution
      (fun (N : ℕ) ω => Real.sqrt (N : ℝ) * (hajek pA pB pD y S N ω - contrast pA pB y))
      atTop Z (fun _ => P) Q := by sorry

end StochSeedEval.Hajek
