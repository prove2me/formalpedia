-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_corollary_3_16
-- name    : SU2Eposic.Extreme.corollary_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:38.314735+00:00
-- url     : https://prove2.me/theorems/cb6372bd-196c-4cf2-aa08-b005b1e96797
-- title:
--   Corollary 3.16 — EC(r, m) spans the SU(2)-equivariant linear maps End(P_r) → End(P_m)
-- statement:
--   Let $r,m\in\mathbb N$. Then $EC(r,m)$ is a spanning set of the vector space $\mathrm{End}(\mathrm{End}(P_r),\mathrm{End}(P_m))^{SU(2)}$ of SU(2)-equivariant linear maps: a linear map $\Phi:\mathrm{End}(P_r)\to\mathrm{End}(P_m)$ satisfies
--   $$\Phi(\rho_r(g)A\rho_r(g)^*)=\rho_m(g)\Phi(A)\rho_m(g)^*\quad\text{for all }A,\ g\in SU(2)$$
--   if and only if $\Phi$ is a complex linear combination of the EPOSIC channels in $EC(r,m)$.
--
--   Together with positivity and trace preservation this leads to the description of covariant channels as convex combinations of EPOSIC channels (Corollary 3.17).
--
--   **Formalization Note** $P_k$ is represented by coordinates in its canonical orthonormal basis $f^k_l=x_1^lx_2^{k-l}/\sqrt{l!(k-l)!}$, $l=0,\dots,k$ (0-based indices); $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices, adjoints are conjugate transposes, and $P_m\otimes P_n$ is indexed with the $P_m$ factor first. The conjugate space $\bar P_k$ has the same coordinates and carries the entrywise conjugate matrices $\overline{\rho_k(g)}$. Channels are maps on matrices given by a finite normalized Kraus family. The Choi matrix is $C(\Phi)=\sum_{ij}\Phi(E_{ij})\otimes E_{ij}$, output factor first. The relation $r=m+n-2h$ is carried as the hypothesis $r+2h=m+n$. The "if" direction records that $EC(r,m)$ lies in the space it spans (the EPOSIC channels are linear and equivariant).
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 25, Corollary 3.16

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Setup

namespace SU2Eposic.Extreme

open scoped Matrix

/-- **Corollary 3.16, p. 25.** `EC(r, m)` is a spanning set of the space
`End(End(P_r), End(P_m))^{SU(2)}` of SU(2)-equivariant linear maps: a linear map
`Φ : End(P_r) → End(P_m)` satisfies `Φ(ρ_r(g) A ρ_r(g)*) = ρ_m(g) Φ(A) ρ_m(g)*` for all `g, A` if
and only if it is a complex linear combination of EPOSIC channels in `EC(r, m)`. -/
theorem corollary_3_16 (r m : ℕ)
    (Φ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ →ₗ[ℂ] Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    (∀ (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
        Φ (rho r g * A * (rho r g)ᴴ) = rho m g * Φ A * (rho m g)ᴴ) ↔
      (⇑Φ : QAlgorithms.Superop (Fin (r + 1)) (Fin (m + 1))) ∈ Submodule.span ℂ (EC r m) := by sorry

end SU2Eposic.Extreme
