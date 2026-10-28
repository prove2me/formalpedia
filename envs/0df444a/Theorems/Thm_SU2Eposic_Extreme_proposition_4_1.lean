-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_proposition_4_1
-- name    : SU2Eposic.Extreme.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:42.319869+00:00
-- url     : https://prove2.me/theorems/9bd3fc6d-79ed-4283-a768-f2aea273f87c
-- title:
--   Proposition 4.1 — the extreme points of QC_{SU(2)}(ρ_r, ρ_m) are exactly the EPOSIC channels EC(r, m)
-- statement:
--   Let $r,m\in\mathbb N$. The set of extreme points of the convex set $QC_{SU(2)}(\rho_r,\rho_m)$ of SU(2)-covariant quantum channels from $\mathrm{End}(P_r)$ to $\mathrm{End}(P_m)$ is the set of EPOSIC channels:
--   $$\operatorname{ext}\,QC_{SU(2)}(\rho_r,\rho_m)=EC(r,m)=\{\Phi_{m,n,h}:\ r=m+n-2h,\ 0\le h\le\min\{m,n\}\}.$$
--
--   Here $\rho_k$ is the irreducible representation of $SU(2)$ on homogeneous polynomials of degree $k$ in two variables, $\Phi_{m,n,h}(A)=\mathrm{Tr}_{P_n}(\alpha_{m,n,h}A\alpha^*_{m,n,h})$, and $\alpha_{m,n,h}=\sqrt{c_{m,n,h}}\,\Gamma_{xy}^h\Delta_{yx}^{n-h}$ is the explicit Clebsch–Gordan isometry. This is the paper's main result: the covariant channels form a simplex whose vertices are the EPOSIC channels.
--
--   **Formalization Note** $P_k$ is represented by coordinates in its canonical orthonormal basis $f^k_l=x_1^lx_2^{k-l}/\sqrt{l!(k-l)!}$, $l=0,\dots,k$ (0-based indices); $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices, adjoints are conjugate transposes, and $P_m\otimes P_n$ is indexed with the $P_m$ factor first. The conjugate space $\bar P_k$ has the same coordinates and carries the entrywise conjugate matrices $\overline{\rho_k(g)}$. Channels are maps on matrices given by a finite normalized Kraus family. The Choi matrix is $C(\Phi)=\sum_{ij}\Phi(E_{ij})\otimes E_{ij}$, output factor first. The relation $r=m+n-2h$ is carried as the hypothesis $r+2h=m+n$. Extreme points are taken for the real-linear structure on maps between matrix spaces.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 26, Proposition 4.1

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Setup

namespace SU2Eposic.Extreme

/-- **Proposition 4.1, p. 26.** For `r, m ∈ ℕ`, the set of extreme points of the (real) convex set
`QC_{SU(2)}(ρ_r, ρ_m)` is `EC(r, m)`. -/
theorem proposition_4_1 (r m : ℕ) : Set.extremePoints ℝ (QC r m) = EC r m := by sorry

end SU2Eposic.Extreme
