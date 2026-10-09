-- Prove2me | Theorems.Thm_WassVarReg_PInf_regularizer_eq_avg_G
-- name    : WassVarReg.PInf.regularizer_eq_avg_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:48.30859+00:00
-- url     : https://prove2.me/theorems/17927814-9644-4fd7-aae8-ec8d2278face
-- title:
--   Proof of Lemma EC.9(I), p. ec8 — empirical regularizer equals average local growth
-- statement:
--   Let $z_1,\ldots,z_n$ be a nonempty sample, let $P_n=n^{-1}\sum_{i=1}^{n}\delta_{z_i}$, and let $f$ be measurable. Write $G_f(\delta,z)=\sup\{f(\tilde z)-f(z): d(\tilde z,z)\le\delta\}$ for the local growth of $f$. For every $\rho\ge0$,
--   $$
--   R_{P_n,\infty}(\rho;f)=\frac1n\sum_{i=1}^{n}G_f(\rho,z_i)
--   =\sup\Bigl\{\frac1n\sum_{i=1}^{n}G_f(\delta_i,z_i): 0\le\delta_i\le\rho,\ 1\le i\le n\Bigr\}.
--   $$
--   This is the identity displayed in the proof of Lemma EC.9(I) (and, in its first form, in the proof of Lemma 1(I)), without the finite term $\rho\,\frac1n\sum_i|\partial f|(z_i)$ that the page subtracts from both sides. It turns the supremum over all probability laws in the $\infty$-Wasserstein ball into a finite average of pointwise local quantities, which is what the main estimate then bounds term by term.
--
--   **Formalization Note** The equality is in the extended reals, so it also covers a loss unbounded above on a radius-$\rho$ ball. The sample indices are `Fin n`, and the metric space is second countable with its Borel structure.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), proof of Lemma EC.9(I), p. ec8 (PDF p. 31); first equality also in proof of Lemma 1(I), p. ec6 (PDF p. 29)

import Mathlib
import Definitions.Def_WassVarReg_PInf_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace WassVarReg.PInf

/-- The identity in the proof of Lemma EC.9(I), p. ec8 (and Lemma 1(I), p. ec6),
without the common finite shift `ρ ‖|∂f|‖_{P_n,1}`: the empirical robust regularizer is
the average local growth at radius `ρ`, and also the page's supremum over per-sample
radii `0 ≤ δ_i ≤ ρ`. -/
theorem regularizer_eq_avg_G {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Z) (f : Z → ℝ)
    (hf : Measurable f) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    regularizerInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f =
        ((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, Gf f ρ (ω i) ∧
      regularizerInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f =
        ⨆ (δ : Fin n → ℝ) (_ : ∀ i, 0 ≤ δ i ∧ δ i ≤ ρ),
          ((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, Gf f (δ i) (ω i) := by sorry

end WassVarReg.PInf
