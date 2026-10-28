-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_corollary_3_17
-- name    : SU2Eposic.Extreme.corollary_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:46.73665+00:00
-- url     : https://prove2.me/theorems/fb0a55c4-a434-4e6d-b909-cccedf864b16
-- title:
--   Corollary 3.17 — QC_{SU(2)}(ρ_r, ρ_m) is the convex hull of EC(r, m)
-- statement:
--   Let $r,m\in\mathbb N$. The set $QC_{SU(2)}(\rho_r,\rho_m)$ of SU(2)-covariant quantum channels from $\mathrm{End}(P_r)$ to $\mathrm{End}(P_m)$ is the convex hull of the set $EC(r,m)$ of EPOSIC channels:
--   $$QC_{SU(2)}(\rho_r,\rho_m)=\mathrm{Conv}\big(EC(r,m)\big).$$
--
--   Every covariant channel is therefore a convex mixture of the finitely many EPOSIC channels.
--
--   **Formalization Note** $P_k$ is represented by coordinates in its canonical orthonormal basis $f^k_l=x_1^lx_2^{k-l}/\sqrt{l!(k-l)!}$, $l=0,\dots,k$ (0-based indices); $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices, adjoints are conjugate transposes, and $P_m\otimes P_n$ is indexed with the $P_m$ factor first. The conjugate space $\bar P_k$ has the same coordinates and carries the entrywise conjugate matrices $\overline{\rho_k(g)}$. Channels are maps on matrices given by a finite normalized Kraus family. The Choi matrix is $C(\Phi)=\sum_{ij}\Phi(E_{ij})\otimes E_{ij}$, output factor first. The relation $r=m+n-2h$ is carried as the hypothesis $r+2h=m+n$. Convex combinations are real convex combinations of maps, taken pointwise.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 26, Corollary 3.17

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Setup

namespace SU2Eposic.Extreme

/-- **Corollary 3.17, p. 26.** `QC_{SU(2)}(ρ_r, ρ_m)` is the convex hull (over `ℝ`) of
`EC(r, m)`. -/
theorem corollary_3_17 (r m : ℕ) : QC r m = convexHull ℝ (EC r m) := by sorry

end SU2Eposic.Extreme
