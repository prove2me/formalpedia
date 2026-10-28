-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_proposition_2_18
-- name    : SU2Eposic.Extreme.proposition_2_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:32.622553+00:00
-- url     : https://prove2.me/theorems/f588a41b-e67e-41ca-937b-11ff079fc40c
-- title:
--   Proposition 2.18 — Φ_{m,n,h} is an SU(2)-irreducibly covariant channel
-- statement:
--   Let $m,n,h\in\mathbb N$ with $0\le h\le\min\{m,n\}$ and $r=m+n-2h$. The map $\Phi_{m,n,h}:\mathrm{End}(P_r)\to\mathrm{End}(P_m)$,
--   $$\Phi_{m,n,h}(A)=\mathrm{Tr}_{P_n}\big(\alpha_{m,n,h}A\alpha^*_{m,n,h}\big),\qquad A\in\mathrm{End}(P_r),$$
--   is a quantum channel satisfying $\Phi_{m,n,h}(\rho_r(g)A\rho_r(g)^*)=\rho_m(g)\Phi_{m,n,h}(A)\rho_m(g)^*$ for all $A$ and all $g\in SU(2)$; that is, $\Phi_{m,n,h}\in QC_{SU(2)}(\rho_r,\rho_m)$.
--
--   These are the EPOSIC channels; the paper's main result identifies them as the extreme points of $QC_{SU(2)}(\rho_r,\rho_m)$.
--
--   **Formalization Note** $P_k$ is represented by coordinates in its canonical orthonormal basis $f^k_l=x_1^lx_2^{k-l}/\sqrt{l!(k-l)!}$, $l=0,\dots,k$ (0-based indices); $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices, adjoints are conjugate transposes, and $P_m\otimes P_n$ is indexed with the $P_m$ factor first. The conjugate space $\bar P_k$ has the same coordinates and carries the entrywise conjugate matrices $\overline{\rho_k(g)}$. Channels are maps on matrices given by a finite normalized Kraus family. The Choi matrix is $C(\Phi)=\sum_{ij}\Phi(E_{ij})\otimes E_{ij}$, output factor first. The relation $r=m+n-2h$ is carried as the hypothesis $r+2h=m+n$. The word *irreducibly* refers to the irreducibility of $\rho_r$ and $\rho_m$ (Proposition 2.1(2), cited in the paper); the membership statement does not depend on it.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 18, Proposition 2.18

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Setup

namespace SU2Eposic.Extreme

/-- **Proposition 2.18, p. 18.** For `0 ≤ h ≤ min{m, n}` and `r = m + n − 2h`, the map
`Φ_{m,n,h}(A) = Tr_{P_n}(α_{m,n,h} A α*_{m,n,h})` is an SU(2)-covariant channel from End(P_r) to
End(P_m): it lies in `QC_{SU(2)}(ρ_r, ρ_m)`. -/
theorem proposition_2_18 (r m n h : ℕ) (hr : r + 2 * h = m + n) (hm : h ≤ m) (hn : h ≤ n) :
    eposic r m n h ∈ QC r m := by sorry

end SU2Eposic.Extreme
