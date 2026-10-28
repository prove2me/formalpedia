-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_proposition_1_15
-- name    : SU2Eposic.Extreme.proposition_1_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:42.191009+00:00
-- url     : https://prove2.me/theorems/0ed3a869-6554-4512-9ba8-14b6fde49de7
-- title:
--   Proposition 1.15(1) — Φ is SU(2)-equivariant iff its Choi matrix lies in the commutant (ρ_m ⊗ ρ̌_r)′
-- statement:
--   Let $r,m\in\mathbb N$ and let $\Phi:\mathrm{End}(P_r)\to\mathrm{End}(P_m)$ be a linear map. Then $\Phi$ is SU(2)-equivariant,
--   $$\Phi(\rho_r(g)A\rho_r(g)^*)=\rho_m(g)\Phi(A)\rho_m(g)^*\quad\text{for all }A\in\mathrm{End}(P_r),\ g\in SU(2),$$
--   if and only if its Choi matrix $C(\Phi)$ belongs to the commutant $(\rho_m\otimes\check\rho_r(SU(2)))'$, i.e. commutes with $\rho_m(g)\otimes\bar\rho_r(g)$ for every $g\in SU(2)$.
--
--   The paper cites this from [4] for a general group and representations $\pi_H,\pi_K$; it is stated here for the case used, $G=SU(2)$, $\pi_H=\rho_r$, $\pi_K=\rho_m$. It converts covariance of channels into a statement about a commutant.
--
--   **Formalization Note** $P_k$ is represented by coordinates in its canonical orthonormal basis $f^k_l=x_1^lx_2^{k-l}/\sqrt{l!(k-l)!}$, $l=0,\dots,k$ (0-based indices); $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices, adjoints are conjugate transposes, and $P_m\otimes P_n$ is indexed with the $P_m$ factor first. The conjugate space $\bar P_k$ has the same coordinates and carries the entrywise conjugate matrices $\overline{\rho_k(g)}$. Channels are maps on matrices given by a finite normalized Kraus family. The Choi matrix is $C(\Phi)=\sum_{ij}\Phi(E_{ij})\otimes E_{ij}$, output factor first. The relation $r=m+n-2h$ is carried as the hypothesis $r+2h=m+n$. The contragredient $\check\rho_r$ coincides with the conjugate representation $\bar\rho_r$ since $\rho_r$ is unitary.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 7, Proposition 1.15(1) (cited from [4]); specialized to G = SU(2), π_H = ρ_r, π_K = ρ_m

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Choi

namespace SU2Eposic.Extreme

open scoped Matrix Kronecker

/-- **Proposition 1.15(1), p. 7** (cited in the paper from [4]), for `G = SU(2)`,
`π_H = ρ_r`, `π_K = ρ_m`. A linear map `Φ : End(P_r) → End(P_m)` is SU(2)-equivariant,
`Φ(ρ_r(g) A ρ_r(g)*) = ρ_m(g) Φ(A) ρ_m(g)*` for all `g, A`, if and only if its Choi matrix
`C(Φ)` lies in the commutant `(ρ_m ⊗ ρ̌_r(SU(2)))′`, i.e. commutes with every `ρ_m(g) ⊗ ρ̄_r(g)`. -/
theorem proposition_1_15 (r m : ℕ)
    (Φ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ →ₗ[ℂ] Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    (∀ (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
        Φ (rho r g * A * (rho r g)ᴴ) = rho m g * Φ A * (rho m g)ᴴ) ↔
      ∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        Commute (choi (⇑Φ : QAlgorithms.Superop (Fin (r + 1)) (Fin (m + 1))))
          (rho m g ⊗ₖ rhoConj r g) := by sorry

end SU2Eposic.Extreme
