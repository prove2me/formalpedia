-- Prove2me | Theorems.Thm_ScutaruFid_kernel_comp
-- name    : ScutaruFid.kernel_comp
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:58.03106+00:00
-- url     : https://prove2.me/theorems/07446a59-98e8-40e6-bf0e-138a0da35b9c
-- title:
--   Eq. (4): the kernel of $\rho_1\rho_2$ is $\int\langle x|\rho_1|z\rangle\langle z|\rho_2|y\rangle\,dz$
-- statement:
--   Let $\rho_1,\rho_2$ be density operators on $L^2(\mathbb R)$ whose kernels $\langle x|\rho_j|y\rangle$ are Gaussian kernels (3) with complex parameters $(a_j,b_j,d_j,l_j,k_j,g_j)$, $j=1,2$. Then the product $\rho_1\rho_2$ is the integral operator with kernel
--
--   $$
--   \langle x|\rho_1\rho_2|y\rangle=\int_{-\infty}^{+\infty}\langle x|\rho_1|z\rangle\langle z|\rho_2|y\rangle\,dz .
--   $$
--
--   This semigroup composition law, together with the evaluation of the Gaussian integral (rule R1), shows that products of Gaussian density operators stay in the oscillator semigroup.
--
--   Differences from the source:
--   - reading: two quantum density operators ρ1, ρ2 (in the paragraph on Gaussian density operators (2)–(3)) → two density operators whose kernels are Gaussian kernels (3); reason: the law is stated between (3) and (5), and the next sentence names "the corresponding parameters of the Gaussian <x|ρ1ρ2|y>", so ρ1, ρ2 are the Gaussian density operators of (3)
--   - encoding: density operator → IsDensityOperator B ρ in an arbitrary Hilbert basis B; reason: basis-independent trace
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eq. (4), p.1

import Mathlib
import Definitions.Def_ScutaruFid_L2R
import Definitions.Def_ScutaruFid_IsKernelOperator
import Definitions.Def_ScutaruFid_gaussKernel
import Definitions.Def_ScutaruFid_IsDensityOperator

namespace ScutaruFid

/-- **Semigroup composition law**, eq. (4). Scutaru, arXiv:quant-ph/9708013v1, eq. (4), p.1: "For
two quantum density operators ρ1 and ρ2 we have the semigroup composition law
<x|ρ1ρ2|y> = ∫_{−∞}^{+∞} <x|ρ1|z><z|ρ2|y> dz".

If `ρ₁`, `ρ₂` are density operators on `L²(ℝ)` with Gaussian kernels `K₁`, `K₂` of the form (3),
then the product `ρ₁ρ₂` is the integral operator with kernel `(x, y) ↦ ∫ K₁(x, z) K₂(z, y) dz`.

**Formalization Note** "Density operator" is `IsDensityOperator B ρᵢ` for a Hilbert basis `B`
(trace class, positive, trace one); the kernels are `gaussKernel` with arbitrary complex
parameters. -/
theorem kernel_comp {ι : Type*} (B : HilbertBasis ι ℂ L2R) (ρ₁ ρ₂ : L2R →L[ℂ] L2R)
    (a₁ b₁ d₁ l₁ k₁ g₁ a₂ b₂ d₂ l₂ k₂ g₂ : ℂ)
    (hρ₁ : IsDensityOperator B ρ₁) (hρ₂ : IsDensityOperator B ρ₂)
    (hK₁ : IsKernelOperator ρ₁ (gaussKernel a₁ b₁ d₁ l₁ k₁ g₁))
    (hK₂ : IsKernelOperator ρ₂ (gaussKernel a₂ b₂ d₂ l₂ k₂ g₂)) :
    IsKernelOperator (ρ₁ * ρ₂) (fun x y => ∫ z : ℝ,
      gaussKernel a₁ b₁ d₁ l₁ k₁ g₁ x z * gaussKernel a₂ b₂ d₂ l₂ k₂ g₂ z y) := by sorry

end ScutaruFid
