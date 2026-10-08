-- Prove2me | Theorems.Thm_RogersSatchell_Unbiased_wiener_hopf_split
-- name    : RogersSatchell.Unbiased.wiener_hopf_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:23.277162+00:00
-- url     : https://prove2.me/theorems/ad751c27-d8fa-45ca-a004-dd5968b7bca6
-- title:
--   Section 2, p. 505 — Wiener–Hopf: S_T and S_T − X_T are independent and S_T − X_T has the law of −I_T
-- statement:
--   Let $B$ be a standard Brownian motion with every sample path continuous, $c\in\mathbb R$, $\sigma\ge0$, $X_t=\sigma B_t+ct$, with running maximum $S_t$ and running minimum $I_t$ over $[0,t]$. Let $T$ be exponential with rate $\lambda>0$, independent of the path $B$. Then
--
--   1. $S_T$ and $S_T-X_T$ are independent, and
--   2. $S_T-X_T$ has the same law as $-I_T$:
--   $$\mathcal L(S_T-X_T)=\mathcal L(-I_T).$$
--
--   This is the splitting at the maximum given by the classical Wiener–Hopf factorisation of the Lévy process $X$ (the paper cites Greenwood and Pitman). It reduces expectations of products $S_T\cdot(S_T-X_T)$ to products of the means of $S_T$ and $-I_T$.
--
--   **Formalization Note** Equality of laws is equality of the image measures $P\circ(S_T-X_T)^{-1}=P\circ(-I_T)^{-1}$; because the image of a non-measurable map is the zero measure in Mathlib, the statement also asserts that both maps are almost-everywhere measurable. Independence of $T$ from $B$ is independence from the whole path. The splitting includes $\sigma=0$, when $X_t=ct$ is deterministic, as the paper's standing model permits.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), Section 2, p. 505

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process

open MeasureTheory ProbabilityTheory NNReal

namespace RogersSatchell.Unbiased

/-- Rogers–Satchell 1991, §2, p. 505 (Wiener–Hopf factorisation): at an independent exponential time
`T`, `S_T` and `S_T − X_T` are independent, and `S_T − X_T` has the same law as `−I_T`. -/
theorem wiener_hopf_split
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ)
    (lam : ℝ) (hlam : 0 < lam) (T : Ω → ℝ) (hT : HasLaw T (expMeasure lam) P)
    (hTB : IndepFun T (fun ω => fun t => B t ω) P) :
    AEMeasurable (fun ω => runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω) P ∧
    AEMeasurable (fun ω => - runMin σ c B (T ω).toNNReal ω) P ∧
    IndepFun (fun ω => runMax σ c B (T ω).toNNReal ω)
      (fun ω => runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω) P ∧
    P.map (fun ω => runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω) =
      P.map (fun ω => - runMin σ c B (T ω).toNNReal ω) := by sorry

end RogersSatchell.Unbiased
