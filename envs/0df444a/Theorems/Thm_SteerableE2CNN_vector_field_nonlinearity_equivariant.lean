-- Prove2me | Theorems.Thm_SteerableE2CNN_vector_field_nonlinearity_equivariant
-- name    : SteerableE2CNN.vector_field_nonlinearity_equivariant
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:40:36.354363+00:00
-- url     : https://prove2.me/theorems/fb6f45ff-f2d8-4a9a-a355-24e31dc06991
-- title:
--   Appendix D.2.4 (as proved): vector field nonlinearities map regular fields to vector fields
-- statement:
--   Let $N\ge1$ and let $\rho_{\mathrm{reg}}$ be the regular representation of $C_N$ on $\mathbb{R}^N$, with axes $e_p$ ($p\in\mathbb{Z}/N$, corresponding to the angles $2\pi p/N$) and $\rho_{\mathrm{reg}}(\tilde p)e_p=e_{\tilde p+p}$. The vector field nonlinearity is
--
--   $$\sigma_{\mathrm{vec}}(f)=\max(f)\begin{pmatrix}\cos\theta\\\sin\theta\end{pmatrix},\qquad\theta=\tfrac{2\pi}{N}\arg\max(f).$$
--
--   If $f\in\mathbb{R}^N$ has a unique maximal entry, then for every $\tilde p\in\mathbb{Z}/N$
--
--   $$\sigma_{\mathrm{vec}}\big(\rho_{\mathrm{reg}}(\tilde p)f\big)=\psi\big(\tfrac{2\pi\tilde p}{N}\big)\,\sigma_{\mathrm{vec}}(f),$$
--
--   where $\psi(\alpha)$ is the rotation matrix by $\alpha$. So $\sigma_{\mathrm{vec}}$ maps a regular field to a field that transforms under the standard representation of $C_N$.
--
--   **Formalization Note** The paper states this for every $f$. Its proof uses $\arg\max(\rho_{\mathrm{reg}}(\tilde p)f)=\tilde p+\arg\max(f)$, which holds only when the maximiser is unique. With ties the claim is false. For example, take $N=2$ and $f=(1,1)$: then $\rho_{\mathrm{reg}}(1)f=f$, but $\psi(\pi)\sigma_{\mathrm{vec}}(f)=-\sigma_{\mathrm{vec}}(f)\neq\sigma_{\mathrm{vec}}(f)$. The uniqueness hypothesis is therefore added. Lean's $\arg\max$ is a fixed choice among the maximisers.
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Section 2.6, p. 6; Appendix D.2.4, p. 24

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

open Matrix MeasureTheory

namespace SteerableE2CNN

theorem vector_field_nonlinearity_equivariant (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    (hv : ∃! a : ZMod N, ∀ b, v b ≤ v a) (p : ZMod N) :
    vecFieldNL N (regRepCN N p *ᵥ v) = rotMat (2 * Real.pi * (p.val : ℝ) / N) *ᵥ vecFieldNL N v := by sorry

end SteerableE2CNN
