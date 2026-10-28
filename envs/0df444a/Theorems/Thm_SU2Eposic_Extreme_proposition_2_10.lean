-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_proposition_2_10
-- name    : SU2Eposic.Extreme.proposition_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:59.516379+00:00
-- url     : https://prove2.me/theorems/20d3c184-159d-405e-bacd-2b07eef5cb01
-- title:
--   Proposition 2.10 — α_{m,n,h} is an SU(2)-equivariant isometry
-- statement:
--   Let $m,n,h\in\mathbb N$ with $0\le h\le\min\{m,n\}$ and $r=m+n-2h$. Then $\alpha_{m,n,h}:P_r\to P_m\otimes P_n$ is an isometry and is SU(2)-equivariant:
--   $$\alpha_{m,n,h}^*\alpha_{m,n,h}=I_{P_r},\qquad (\rho_m(g)\otimes\rho_n(g))\,\alpha_{m,n,h}=\alpha_{m,n,h}\,\rho_r(g)\quad\text{for all }g\in SU(2).$$
--
--   So $\alpha_{m,n,h}$ is an explicit Clebsch–Gordan embedding of $P_r$ into $P_m\otimes P_n$, and $(P_n,\alpha_{m,n,h})$ is a Stinespring dilation of a covariant channel.
--
--   **Formalization Note** $P_k$ is represented by coordinates in its canonical orthonormal basis $f^k_l=x_1^lx_2^{k-l}/\sqrt{l!(k-l)!}$, $l=0,\dots,k$ (0-based indices); $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices, adjoints are conjugate transposes, and $P_m\otimes P_n$ is indexed with the $P_m$ factor first. The conjugate space $\bar P_k$ has the same coordinates and carries the entrywise conjugate matrices $\overline{\rho_k(g)}$. Channels are maps on matrices given by a finite normalized Kraus family. The Choi matrix is $C(\Phi)=\sum_{ij}\Phi(E_{ij})\otimes E_{ij}$, output factor first. The relation $r=m+n-2h$ is carried as the hypothesis $r+2h=m+n$.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 12, Proposition 2.10

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Setup

namespace SU2Eposic.Extreme

open scoped Matrix Kronecker

/-- **Proposition 2.10, p. 12.** For `0 ≤ h ≤ min{m, n}` and `r = m + n − 2h`, the map
`α_{m,n,h} : P_r → P_m ⊗ P_n` is an isometry and is SU(2)-equivariant:
`(ρ_m(g) ⊗ ρ_n(g)) α_{m,n,h} = α_{m,n,h} ρ_r(g)` for every `g ∈ SU(2)`. -/
theorem proposition_2_10 (r m n h : ℕ) (hr : r + 2 * h = m + n) (hm : h ≤ m) (hn : h ≤ n) :
    (alpha r m n h)ᴴ * alpha r m n h = 1 ∧
    ∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      (rho m g ⊗ₖ rho n g) * alpha r m n h = alpha r m n h * rho r g := by sorry

end SU2Eposic.Extreme
