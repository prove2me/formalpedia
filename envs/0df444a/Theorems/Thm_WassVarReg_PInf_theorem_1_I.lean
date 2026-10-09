-- Prove2me | Theorems.Thm_WassVarReg_PInf_theorem_1_I
-- name    : WassVarReg.PInf.theorem_1_I
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:42.485339+00:00
-- url     : https://prove2.me/theorems/dac9883b-f724-4ee8-a873-c8274bba6511
-- title:
--   Theorem 1(I), pp. 8, 20 — W∞ regularizer approximates mean local slope
-- statement:
--   Let $(Z,d)$ be a metric space without isolated points, $F$ a family of measurable real losses, and $D_f\subseteq Z$ an associated set for each loss. Suppose there are $\delta_0>0$, $M\ge0$, and a real function $H$ such that, for every $f\in F$, $z\in Z$, and $0\le\delta<\delta_0$,
--   $$
--   \bigl|G_f(\delta,z)-\delta|\partial f|(z)\bigr|
--   \le H(z)\delta^2+M(\delta-d(z,D_f))_+.
--   $$
--   Then some $\bar\rho>0$ works for every nonempty finite sample $z_1,\ldots,z_n$, every $0\le\rho<\bar\rho$, and every $f\in F$. The regularizer is finite and
--   $$
--   \left|R_{P_n,\infty}(\rho;f)-\rho\frac1n\sum_{i=1}^{n}|\partial f|(z_i)\right|
--   \le \rho^2\frac1n\sum_{i=1}^{n}|H(z_i)|
--   +M\frac1n\sum_{i=1}^{n}(\rho-d(z_i,D_f))_+,
--   \quad P_n=\frac1n\sum_{i=1}^{n}\delta_{z_i}.
--   $$
--   The estimate identifies the mean local slope as the first-order regularization term, with quadratic growth and boundary corrections.
--
--   **Formalization Note** This is the general-metric Theorem 1(I) of Appendix B under the replacement Assumption 5(I) on p. 13, as proved in Lemma EC.9(I). (Theorem 1(I) on p. 8 is the Banach form under Assumptions 1–2; its restatement on p. 20 still names Assumptions 1–2, while p. 13 says Assumption 5 replaces them in the metric setting and Lemma EC.9 is stated under Assumption 5.) The radius bound is uniform in the sample, as the proof gives $\bar\rho=\delta_0$. The space has a second-countable Borel structure so transport distance is measurable. Finiteness of slope and local growth is explicit. The statement allows arbitrary $D_f$ and $H$ without assuming $D_f$ is null or $H\in L^1(P_{\rm true})$, because only their sample values occur here. The $\rho_n^2$ printed in Lemma EC.9 is read as $\rho^2$, consistent with Theorem 1(I).
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), Theorem 1(I), p. 8; metric restatement, p. 20; Assumption 5(I), p. 13; Lemma EC.9(I), p. ec8 (PDF p. 31)

import Mathlib
import Definitions.Def_WassVarReg_PInf_Setting

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace WassVarReg.PInf

/-- Theorem 1(I), pp. 8 and 20, in the general metric form under Assumption 5(I)
of p. 13, also the order-infinity part of Lemma EC.9, p. ec8. -/
theorem theorem_1_I {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    (hnoiso : ∀ z : Z, (nhdsWithin z {z}ᶜ).NeBot)
    (F : Set (Z → ℝ)) (hmeas : ∀ f ∈ F, Measurable f)
    (D : (Z → ℝ) → Set Z) (H : Z → ℝ) (δ0 M : ℝ)
    (hδ0 : 0 < δ0) (hM : 0 ≤ M) (hA5 : Assumption5I F D H δ0 M) :
    ∃ ρbar : ℝ, 0 < ρbar ∧
      ∀ (n : ℕ) (hn : 0 < n) (ω : Fin n → Z) (ρ : ℝ),
        0 ≤ ρ → ρ < ρbar → ∀ f ∈ F,
          regularizerInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f ≠ ⊤ ∧
          regularizerInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f ≠ ⊥ ∧
          |(regularizerInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f).toReal -
            ρ * ((1 / (n : ℝ)) * ∑ i : Fin n, (localSlope f (ω i)).toReal)| ≤
            ρ ^ 2 * ((1 / (n : ℝ)) * ∑ i : Fin n, |H (ω i)|) +
              M * ((1 / (n : ℝ)) * ∑ i : Fin n, boundaryGap ρ (D f) (ω i)) := by sorry

end WassVarReg.PInf
