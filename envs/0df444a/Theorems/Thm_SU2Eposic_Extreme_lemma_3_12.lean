-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_lemma_3_12
-- name    : SU2Eposic.Extreme.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:45.179899+00:00
-- url     : https://prove2.me/theorems/4b8008ff-b331-4c3e-a094-753755e27f7d
-- title:
--   Lemma 3.12 — C(Φ_{m,n,h}) η_{m,r,m−h} is non-zero
-- statement:
--   Let $m,n,h\in\mathbb N$ with $0\le h\le\min\{m,n\}$ and $r=m+n-2h$. Then the operator
--   $$C(\Phi_{m,n,h})\,\eta_{m,r,m-h}:P_n\to P_m\otimes\bar P_r$$
--   is non-zero. Here $\eta_{m,r,m-h}$ is defined on $P_{m+r-2(m-h)}=P_n$.
--
--   This shows that the Choi matrix of $\Phi_{m,n,h}$ has a non-zero component along the projection $q_{m,r,m-h}$, which singles out that projection in Proposition 3.13.
--
--   **Formalization Note** $P_k$ is represented by coordinates in its canonical orthonormal basis $f^k_l=x_1^lx_2^{k-l}/\sqrt{l!(k-l)!}$, $l=0,\dots,k$ (0-based indices); $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices, adjoints are conjugate transposes, and $P_m\otimes P_n$ is indexed with the $P_m$ factor first. The conjugate space $\bar P_k$ has the same coordinates and carries the entrywise conjugate matrices $\overline{\rho_k(g)}$. Channels are maps on matrices given by a finite normalized Kraus family. The Choi matrix is $C(\Phi)=\sum_{ij}\Phi(E_{ij})\otimes E_{ij}$, output factor first. The relation $r=m+n-2h$ is carried as the hypothesis $r+2h=m+n$.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 23, Lemma 3.12

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Choi

namespace SU2Eposic.Extreme

/-- **Lemma 3.12, p. 23.** For `0 ≤ h ≤ min{m, n}` and `r = m + n − 2h`, the operator
`C(Φ_{m,n,h}) η_{m,r,m−h}` is non-zero; here `η_{m,r,m−h} : P_n → P_m ⊗ P̄_r`
(`m + r − 2(m − h) = n`). -/
theorem lemma_3_12 (r m n h : ℕ) (hr : r + 2 * h = m + n) (hm : h ≤ m) (hn : h ≤ n) :
    choi (eposic r m n h) * eta n m r (m - h) ≠ 0 := by sorry

end SU2Eposic.Extreme
