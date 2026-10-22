-- Prove2me | Theorems.Thm_RandomGateDesign_MasterBound_theorem_1
-- name    : RandomGateDesign.MasterBound.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:57.821275+00:00
-- url     : https://prove2.me/theorems/99c7c6ff-3dda-49cf-a57b-ec000096f00e
-- title:
--   Theorem 1 — exact design gate-set concentration bound
-- statement:
--   Let $\mu$ be Haar probability measure on $U(d)$ and $\nu$ an exact $t$-design. Draw $S\ge1$ independent gates $U_1,\ldots,U_S$ from $\nu$, and let $\nu_S$ be their empirical measure. For $0<\delta<1$, the spectral operator-norm distance between its mixed tensor moment and the Haar moment satisfies
--
--   $$\Pr\!\left(\left\|T_{\nu_S,t}-T_{\mu,t}\right\|\ge\delta\right)\le\frac{2e^{-\delta S\operatorname{artanh}(\delta)}}{(1-\delta^2)^{S/2}}\sum_{\lambda\in\Lambda_t}d_\lambda.$$
--
--   Here $\Lambda_t$ is the paper's finite set of nonzero dominant weights and $d_\lambda$ is given by the Weyl dimension formula. This is the paper's explicit concentration guarantee for random gates drawn from an exact design.
--
--   **Formalization Note** $\nu_S$ counts draws with multiplicity. The positive threshold corrects the printed phrase “any $\delta<1$”; the bound is false for some nonpositive thresholds.
-- source:
--   Dulian & Sawicki, Matrix concentration inequalities and efficiency of random universal sets of quantum gates, arXiv:2202.05371v3, p. 3, Theorem 1, eq. (3)

import Definitions.Def_RandomGateDesign_MasterBound_Moments

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RandomGateDesign.MasterBound

theorem theorem_1 {d t S : ℕ} (μ ν : Measure (U d))
    (hμ : IsHaarProb μ) (hν : IsExactDesign μ ν t)
    (hS : 1 ≤ S) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi (fun _ : Fin S => ν))
      {Us | δ ≤ TroppMatrixConcentration.spectralNorm
        (empiricalMoment Us t - momentOp μ t)}).toReal ≤
      2 * Real.exp (-(δ * (S : ℝ) * Real.artanh δ)) /
        (1 - δ ^ 2) ^ ((S : ℝ) / 2) *
          ∑ l ∈ Lambda d t, weylDim l := by sorry

end RandomGateDesign.MasterBound
