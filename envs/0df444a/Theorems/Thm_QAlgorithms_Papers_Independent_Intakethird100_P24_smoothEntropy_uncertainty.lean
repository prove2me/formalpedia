-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P24_smoothEntropy_uncertainty
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P24.smoothEntropy_uncertainty
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:11:37.072119+00:00
-- url     : https://prove2.me/theorems/55c2c03a-b31c-4b9f-97d3-582935366890
-- title:
--   Uncertainty relation for smooth min- and max-entropies
-- statement:
--   Let $A,B,C$ be finite-dimensional nonzero quantum systems, and let $\rho_{ABC}\ge0$ satisfy $\operatorname{tr}\rho_{ABC}\le1$. Let $\mathsf X=\{M_x\}_{x\in X}$ and $\mathsf Z=\{N_z\}_{z\in Z}$ be POVMs on $A$ with finite nonempty outcome sets. Thus all effects are positive semidefinite and each family sums to the identity. Define
--   $$
--   c=\max_{x,z}\|\sqrt{M_x}\sqrt{N_z}\|_{\mathrm{op}}^2,\qquad q=-\log_2 c,
--   $$
--   where the operator norm is the largest singular value. From the same input state construct
--   $$
--   \rho_{XB}=\sum_x|x\rangle\langle x|\otimes\operatorname{tr}_{AC}[(M_x\otimes I_{BC})\rho_{ABC}],\qquad
--   \rho_{ZC}=\sum_z|z\rangle\langle z|\otimes\operatorname{tr}_{AB}[(N_z\otimes I_{BC})\rho_{ABC}].
--   $$
--   For every real $\varepsilon\ge0$, the smooth conditional entropies in bits obey
--   $$
--   H_{\min}^{\varepsilon}(X|B)_{\rho_{XB}}\ \ge\ q-H_{\max}^{\varepsilon}(Z|C)_{\rho_{ZC}}.
--   $$
--   Smoothing ranges over all positive semidefinite operators of trace at most one on the respective joint output system, within purified distance $\varepsilon$; perturbations need not be classical. For subnormalized $\omega,\tau$, that distance is $\sqrt{1-\overline F(\omega,\tau)^2}$, where $\overline F(\omega,\tau)=\|\sqrt\omega\sqrt\tau\|_1+\sqrt{(1-\operatorname{tr}\omega)(1-\operatorname{tr}\tau)}$. The unsmoothed min-entropy is the supremum of exponents $\lambda$ with $\rho_{AB}\le2^{-\lambda}I_A\otimes\sigma_B$ for some normalized state $\sigma_B$; max-entropy is its purification dual. The smooth min-entropy takes a supremum and smooth max-entropy takes an infimum over their balls.
--
--   This bounds measurement uncertainty even with distinct quantum side information and without an independence or purity assumption.
--
--   **Formalization Note** The order form agrees with the printed additive inequality whenever finite. If $\varepsilon\ge\sqrt{\operatorname{tr}\rho}$, both balls contain zero, giving $H_{\min}^{\varepsilon}=+\infty$ and $H_{\max}^{\varepsilon}=-\infty$; the order form then reads $+\infty\ge+\infty$. It preserves the zero input and imposes no upper bound on $\varepsilon$.
-- source:
--   The Uncertainty Relation for Smooth Entropies, arXiv:1009.2015v3, PDF p. 2, Theorem 1; equation (4) on PDF p.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P24

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P24

open QAlgorithms.Papers.Independent.Information100.P67
  (IsSubnormalized conditionalMinEntropy conditionalMaxEntropy
   smoothConditionalMinEntropy smoothConditionalMaxEntropyExtended)

open QAlgorithms.Papers.Independent.Dependency50.P35 (measured)

/-- Theorem 1, PDF p.2, equation (4) on p.1; general mixed-state proof on
pp.2--3. Both measured states are computed from the SAME subnormalized rho.
The extended order form is equivalent to the printed sum when finite and
reads +infinity >= +infinity when the smoothing balls contain zero.
No purity, projectivity, normalization, or epsilon < 1 premise is imposed.
At rho = 0 the source's rank-one purification shorthand is interpreted as
the zero extension (rank at most one), as required by its state domain. -/
theorem smoothEntropy_uncertainty
    {A B C X Z : Type}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (rho : Matrix ((A × B) × C) ((A × B) × C) ℂ)
    (hrho : IsSubnormalized rho)
    (M : X → Matrix A A ℂ) (N : Z → Matrix A A ℂ)
    (hM : IsPOVM M) (hN : IsPOVM N) :
    let rhoAC : Matrix (A × C) (A × C) ℂ :=
      fun ac ad => ∑ b : B, rho ((ac.1, b), ac.2) ((ad.1, b), ad.2)
    smoothConditionalMinEntropy (measured M (traceRight rho)) epsilon ≥
      (incompatibilityBits M N : EReal) -
        smoothConditionalMaxEntropyExtended (measured N rhoAC) epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P24

end
