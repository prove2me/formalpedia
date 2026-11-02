-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P24_renyiEndpoints_uncertainty
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P24.renyiEndpoints_uncertainty
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:12:14.426837+00:00
-- url     : https://prove2.me/theorems/f0560501-d4dd-4709-b425-101868547dd2
-- title:
--   POVM uncertainty for Rényi orders infinity and one half
-- statement:
--   Let $\rho\ge0$ have trace at most one on a finite-dimensional nonzero system $A$. Let $\{M_x\}_{x\in X}$ and $\{N_z\}_{z\in Z}$ be two POVMs with finite nonempty outcome sets. Write $p_x=\operatorname{tr}(M_x\rho)$ and $r_z=\operatorname{tr}(N_z\rho)$ for their subnormalized outcome weights, and set
--   $$
--   c=\max_{x,z}\|\sqrt{M_x}\sqrt{N_z}\|_{\mathrm{op}}^2,\qquad q=-\log_2 c.
--   $$
--   The endpoint Rényi entropies in bits satisfy
--   $$
--   H_{\infty}(X)\ge q-H_{1/2}(Z).
--   $$
--   For $\operatorname{tr}\rho>0$, these quantities are $H_{\infty}(X)=-\log_2\max_x p_x$ and $H_{1/2}(Z)=2\log_2\sum_z\sqrt{r_z}$, so this is precisely $H_{\infty}(X)+H_{1/2}(Z)\ge q$. At $\rho=0$, take the endpoint values $+\infty$ and $-\infty$, respectively, and retain the displayed order form.
--
--   This extends the endpoint uncertainty bound to arbitrary finite POVMs and mixed inputs.
--
--   **Formalization Note** The two entropies are the accepted unsmoothed conditional min- and max-entropies of diagonal outcome matrices, each with a one-dimensional conditioning register. No trace renormalization is performed.
-- source:
--   The Uncertainty Relation for Smooth Entropies, arXiv:1009.2015v3, PDF p. 2, Unnumbered consequence, first paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P24

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P24

open QAlgorithms.Papers.Independent.Information100.P67
  (IsSubnormalized conditionalMinEntropy conditionalMaxEntropy
   smoothConditionalMinEntropy smoothConditionalMaxEntropyExtended)

open QAlgorithms.Papers.Independent.Dependency50.P35 (measured)

/-- Unnumbered Renyi endpoint consequence, PDF p.2, first paragraph, with
q from equation (2), PDF p.1. The accepted unsmoothed conditional entropies
on diagonal outcome matrices with a one-dimensional conditioning register
are exactly H_infinity and H_(1/2), including their subnormalized scaling.
The order form handles the zero state without adding opposite infinities. -/
theorem renyiEndpoints_uncertainty
    {A X Z : Type}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (rho : Matrix A A ℂ) (hrho : IsSubnormalized rho)
    (M : X → Matrix A A ℂ) (N : Z → Matrix A A ℂ)
    (hM : IsPOVM M) (hN : IsPOVM N) :
    let rhoX : Matrix (X × Unit) (X × Unit) ℂ :=
      Matrix.diagonal (fun x => (effectProb (M x.1) rho : ℂ))
    let rhoZ : Matrix (Z × Unit) (Z × Unit) ℂ :=
      Matrix.diagonal (fun z => (effectProb (N z.1) rho : ℂ))
    conditionalMinEntropy rhoX ≥
      (incompatibilityBits M N : EReal) - conditionalMaxEntropy rhoZ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P24

end
