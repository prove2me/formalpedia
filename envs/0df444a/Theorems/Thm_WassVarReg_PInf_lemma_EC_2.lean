-- Prove2me | Theorems.Thm_WassVarReg_PInf_lemma_EC_2
-- name    : WassVarReg.PInf.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:00.984904+00:00
-- url     : https://prove2.me/theorems/3ee3a715-f36f-4d37-b08e-60444e127598
-- title:
--   Lemma EC.2, p. ec1 — W∞ strong duality for finite nominal support
-- statement:
--   Let $Q=\sum_{j=1}^{m}q_j\delta_{z_j}$ be a finitely supported probability law on a metric space, let $f$ be measurable, and let $\rho\ge0$. Then the order-infinity Wasserstein robust value equals the finite-support dual value:
--   $$
--   \sup_{P:W_\infty(P,Q)\le\rho}\mathbb E_P[f]
--   =\sum_{j=1}^{m}q_j\sup_{d(\tilde z,z_j)\le\rho}f(\tilde z).
--   $$
--   The identity turns optimization over laws into independent local maximizations at the nominal atoms.
--
--   **Formalization Note** Both sides are extended real and may be $+\infty$; the paper's unqualified finiteness claim is excluded. The metric space is second countable with its Borel structure.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), Lemma EC.2, p. ec1 (PDF p. 24)

import Mathlib
import Definitions.Def_WassVarReg_PInf_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace WassVarReg.PInf

/-- Lemma EC.2, strong order-infinity duality, p. ec1, for a finitely
supported nominal law. The value may be `⊤` for an unbounded loss. -/
theorem lemma_EC_2 {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z] {m : ℕ}
    (q : Fin m → ℝ≥0) (zs : Fin m → Z) (hq : ∑ j, q j = 1)
    (f : Z → ℝ) (hf : Measurable f) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    worstCaseInf ρ (discreteLaw q zs hq) f =
      ∑ j : Fin m, ((q j : ℝ) : EReal) *
        (⨆ (z' : Z) (_ : dist z' (zs j) ≤ ρ), ((f z' : ℝ) : EReal)) := by sorry

end WassVarReg.PInf
