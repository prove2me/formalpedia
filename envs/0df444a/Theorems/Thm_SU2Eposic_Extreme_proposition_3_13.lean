-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_proposition_3_13
-- name    : SU2Eposic.Extreme.proposition_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:40.363516+00:00
-- url     : https://prove2.me/theorems/082f70db-8bbc-4222-a4ae-f0b6ac2af6fb
-- title:
--   Proposition 3.13 — the Choi matrix of Φ_{m,n,h} is (r+1)/(n+1) q_{m,r,m−h}
-- statement:
--   Let $m,n,h\in\mathbb N$ with $0\le h\le\min\{m,n\}$ and $r=m+n-2h$. The Choi matrix of the EPOSIC channel $\Phi_{m,n,h}$ is
--   $$C(\Phi_{m,n,h})=\frac{r+1}{n+1}\,q_{m,r,m-h},$$
--   where $q_{m,r,m-h}$ is the projection of $P_m\otimes\bar P_r$ onto the SU(2)-invariant subspace $V_n$ of dimension $n+1$.
--
--   This gives a one-to-one correspondence between the EPOSIC channels and the projections onto the irreducible summands of $P_m\otimes\bar P_r$ (Remark 3.14).
--
--   **Formalization Note** $P_k$ is represented by coordinates in its canonical orthonormal basis $f^k_l=x_1^lx_2^{k-l}/\sqrt{l!(k-l)!}$, $l=0,\dots,k$ (0-based indices); $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices, adjoints are conjugate transposes, and $P_m\otimes P_n$ is indexed with the $P_m$ factor first. The conjugate space $\bar P_k$ has the same coordinates and carries the entrywise conjugate matrices $\overline{\rho_k(g)}$. Channels are maps on matrices given by a finite normalized Kraus family. The Choi matrix is $C(\Phi)=\sum_{ij}\Phi(E_{ij})\otimes E_{ij}$, output factor first. The relation $r=m+n-2h$ is carried as the hypothesis $r+2h=m+n$.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 24, Proposition 3.13

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Choi

namespace SU2Eposic.Extreme

/-- **Proposition 3.13, p. 24.** For `0 ≤ h ≤ min{m, n}` and `r = m + n − 2h`, the Choi matrix of
the EPOSIC channel `Φ_{m,n,h}` is `(r+1)/(n+1) · q_{m,r,m−h}`, where `q_{m,r,m−h}` is the
projection of `P_m ⊗ P̄_r` onto the SU(2)-invariant subspace `V_n` of dimension `n + 1`. -/
theorem proposition_3_13 (r m n h : ℕ) (hr : r + 2 * h = m + n) (hm : h ≤ m) (hn : h ≤ n) :
    choi (eposic r m n h) = (((r : ℂ) + 1) / ((n : ℂ) + 1)) • q m r (m - h) := by sorry

end SU2Eposic.Extreme
