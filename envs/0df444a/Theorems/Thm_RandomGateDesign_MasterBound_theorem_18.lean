-- Prove2me | Theorems.Thm_RandomGateDesign_MasterBound_theorem_18
-- name    : RandomGateDesign.MasterBound.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:51.350398+00:00
-- url     : https://prove2.me/theorems/393d6dff-8a12-4713-90f0-1891654efe1b
-- title:
--   Theorem 18 — one irreducible block tail bound
-- statement:
--   Let $\mu$ be a Haar probability measure on $U(d)$, and let $\nu$ be an exact $t$-design. Let $\pi:U(d)\to U(m)$ be a continuous, nontrivial, irreducible subrepresentation of $U\mapsto U^{t,t}$. Draw $S\ge1$ independent gates $U_k$ with law $\nu$. For $0<\delta<1$,
--
--   $$\Pr\!\left(\left\|\frac1S\sum_{k=1}^{S}\pi(U_k)\right\|\ge\delta\right)\le \frac{2m\,e^{-\delta S\operatorname{artanh}(\delta)}}{(1-\delta^2)^{S/2}}=\frac{2m}{(1+\delta)^{S(1+\delta)/2}(1-\delta)^{S(1-\delta)/2}}.$$
--
--   This is the individual representation bound summed in Theorem 1.
--
--   **Formalization Note** The paper labels the block by $\lambda\in\Lambda_t$; here its equivalent intrinsic conditions are used, and $m=d_\lambda$. The strict lower bound on $\delta$ corrects the false negative-threshold case of the printed wording.
-- source:
--   Dulian & Sawicki, Matrix concentration inequalities and efficiency of random universal sets of quantum gates, arXiv:2202.05371v3, pp. 21–22, Theorem 18

import Definitions.Def_RandomGateDesign_MasterBound_Reps

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RandomGateDesign.MasterBound

theorem theorem_18 {d t m S : ℕ} (μ ν : Measure (U d))
    (hμ : IsHaarProb μ) (hν : IsExactDesign μ ν t)
    (π : U d →* U m)
    (hπc : Continuous (fun g : U d => (π g : Matrix (Fin m) (Fin m) ℂ)))
    (hπi : IsIrreducible π) (hπn : IsNontrivial π)
    (hπs : IsMomentSubrep t π) (hS : 1 ≤ S)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi (fun _ : Fin S => ν))
      {Us | δ ≤ TroppMatrixConcentration.spectralNorm
        ((S : ℂ)⁻¹ • ∑ k : Fin S,
          (π (Us k) : Matrix (Fin m) (Fin m) ℂ))}).toReal ≤
      2 * (m : ℝ) * Real.exp (-(δ * (S : ℝ) * Real.artanh δ)) /
        (1 - δ ^ 2) ^ ((S : ℝ) / 2) ∧
    2 * (m : ℝ) /
      ((1 + δ) ^ ((S : ℝ) * (1 + δ) / 2) *
        (1 - δ) ^ ((S : ℝ) * (1 - δ) / 2)) =
      2 * (m : ℝ) * Real.exp (-(δ * (S : ℝ) * Real.artanh δ)) /
        (1 - δ ^ 2) ^ ((S : ℝ) / 2) := by sorry

end RandomGateDesign.MasterBound
