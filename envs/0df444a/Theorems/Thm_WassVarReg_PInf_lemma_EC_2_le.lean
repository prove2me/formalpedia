-- Prove2me | Theorems.Thm_WassVarReg_PInf_lemma_EC_2_le
-- name    : WassVarReg.PInf.lemma_EC_2_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:41.185529+00:00
-- url     : https://prove2.me/theorems/aa718751-0d27-413a-954f-49a40a133638
-- title:
--   Lemma EC.2, p. ec1 — primal value is at most the finite-support dual value
-- statement:
--   Let $Q=\sum_{j=1}^{m}q_j\delta_{z_j}$ be a finitely supported probability law on a metric space, let $f$ be measurable, and let $\rho\ge0$. The robust expected loss satisfies
--   $$
--   \sup_{P:W_\infty(P,Q)\le\rho}\mathbb E_P[f]
--   \le \sum_{j=1}^{m}q_j\sup_{d(\tilde z,z_j)\le\rho}f(\tilde z).
--   $$
--   This is the first inequality of the order-infinity strong-duality lemma and bounds every admissible perturbation by its local worst-case losses.
--
--   **Formalization Note** The values are extended real, so an unbounded loss may yield $+\infty$. The paper's extra assertion that the right side is always finite is omitted because it is false without a boundedness condition. The metric space is second countable with its Borel structure.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), Lemma EC.2 and proof, p. ec1 (PDF p. 24)

import Mathlib
import Definitions.Def_WassVarReg_PInf_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace WassVarReg.PInf

/-- Lemma EC.2, first inequality, p. ec1, for a finitely supported nominal law.
The dual value is allowed to be infinite when the loss is unbounded on a ball. -/
theorem lemma_EC_2_le {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z] {m : ℕ}
    (q : Fin m → ℝ≥0) (zs : Fin m → Z) (hq : ∑ j, q j = 1)
    (f : Z → ℝ) (hf : Measurable f) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    worstCaseInf ρ (discreteLaw q zs hq) f ≤
      ∑ j : Fin m, ((q j : ℝ) : EReal) *
        (⨆ (z' : Z) (_ : dist z' (zs j) ≤ ρ), ((f z' : ℝ) : EReal)) := by sorry

end WassVarReg.PInf
