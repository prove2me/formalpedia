-- Prove2me | Theorems.Thm_SteerableE2CNN_kernel_basis_equivalent_representations
-- name    : SteerableE2CNN.kernel_basis_equivalent_representations
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:38:43.546281+00:00
-- url     : https://prove2.me/theorems/aad99e1c-e630-4614-a9e3-4252e49555fe
-- title:
--   Section 2.6: changes of basis between equivalent representations are irrelevant
-- statement:
--   Let $G\le\mathrm{O}(2)$, let $\rho_{\mathrm{in}},\rho_{\mathrm{out}}$ be representations of $G$, and let $P_{\mathrm{in}},P_{\mathrm{out}}$ be invertible matrices. Consider the equivalent representations $\widetilde\rho_{\mathrm{in}}=P_{\mathrm{in}}^{-1}\rho_{\mathrm{in}}P_{\mathrm{in}}$ and $\widetilde\rho_{\mathrm{out}}=P_{\mathrm{out}}^{-1}\rho_{\mathrm{out}}P_{\mathrm{out}}$. A kernel $k$ is $G$-steerable for $(\rho_{\mathrm{in}},\rho_{\mathrm{out}})$ if and only if $P_{\mathrm{out}}^{-1}kP_{\mathrm{in}}$ is $G$-steerable for $(\widetilde\rho_{\mathrm{in}},\widetilde\rho_{\mathrm{out}})$:
--
--   $$k(gx)=\rho_{\mathrm{out}}(g)k(x)\rho_{\mathrm{in}}(g)^{-1}\ \forall g,x\iff (P_{\mathrm{out}}^{-1}kP_{\mathrm{in}})(gx)=\widetilde\rho_{\mathrm{out}}(g)(P_{\mathrm{out}}^{-1}kP_{\mathrm{in}})(x)\widetilde\rho_{\mathrm{in}}(g)^{-1}\ \forall g,x.$$
--
--   Hence a kernel basis $\{k_i\}$ for $(\rho_{\mathrm{in}},\rho_{\mathrm{out}})$ gives the basis $\{P_{\mathrm{out}}^{-1}k_iP_{\mathrm{in}}\}$ for the equivalent pair. For the convolution alone, the choice among equivalent representations is irrelevant.
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Section 2.6, first paragraph, p. 5

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

open Matrix MeasureTheory

namespace SteerableE2CNN

theorem kernel_basis_equivalent_representations (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρin : MatRep G n) (ρout : MatRep G m)
    (Pin : Matrix.GeneralLinearGroup n ℝ) (Pout : Matrix.GeneralLinearGroup m ℝ)
    (k : Plane → Matrix m n ℝ) :
    IsSteerable G ρin ρout k ↔
      KernelConstraint (fun g : G => gMat g)
        (fun g => (↑Pout⁻¹ : Matrix m m ℝ) * repMat ρout g * (↑Pout : Matrix m m ℝ))
        (fun g => (↑Pin⁻¹ : Matrix n n ℝ) * repMat ρin g * (↑Pin : Matrix n n ℝ))
        (fun x => (↑Pout⁻¹ : Matrix m m ℝ) * k x * (↑Pin : Matrix n n ℝ)) := by sorry

end SteerableE2CNN
