-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_corollary_2_13
-- name    : SU2Eposic.Extreme.corollary_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:45.63465+00:00
-- url     : https://prove2.me/theorems/9148ada2-e2dd-47be-b47d-819e399c0f90
-- title:
--   Corollary 2.13 — orthogonal decomposition of P_m ⊗ P̄_n by the projections η η*
-- statement:
--   Let $m,n\in\mathbb N$, and for $0\le h\le\min\{m,n\}$ let $\eta_{m,n,h}=(I_{P_m}\otimes J_n)\alpha_{m,n,h}:P_{m+n-2h}\to P_m\otimes\bar P_n$ and $V_{m+n-2h}=\eta_{m,n,h}(P_{m+n-2h})$. Then for each such $h$:
--
--   1. $\eta_{m,n,h}$ is an isometry, $\eta^*_{m,n,h}\eta_{m,n,h}=I$, intertwining $\rho_{m+n-2h}$ with $\rho_m\otimes\bar\rho_n$, so $V_{m+n-2h}\cong P_{m+n-2h}$ as SU(2)-spaces;
--   2. $\eta_{m,n,h}\eta^*_{m,n,h}$ is the orthogonal projection onto $V_{m+n-2h}$ (self-adjoint and idempotent);
--   3. $V_{m+n-2h}$ is SU(2)-irreducible: for every operator $T$ commuting with all $\rho_m(g)\otimes\bar\rho_n(g)$, the compression $\eta\eta^*\,T\,\eta\eta^*$ is a scalar multiple of $\eta\eta^*$.
--
--   Moreover the projections are mutually orthogonal and sum to the identity, so
--   $$P_m\otimes\bar P_n=\bigoplus_{h=0}^{\min\{m,n\}}V_{m+n-2h}$$
--   is an orthogonal sum of SU(2)-irreducible subspaces.
--
--   The projections $\eta\eta^*$ (written $q_{m,n,h}$) are the building blocks of the commutant of $\rho_m\otimes\bar\rho_n$ and of the Choi matrices of EPOSIC channels.
--
--   **Formalization Note** $P_k$ is represented by coordinates in its canonical orthonormal basis $f^k_l=x_1^lx_2^{k-l}/\sqrt{l!(k-l)!}$, $l=0,\dots,k$ (0-based indices); $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices, adjoints are conjugate transposes, and $P_m\otimes P_n$ is indexed with the $P_m$ factor first. The conjugate space $\bar P_k$ has the same coordinates and carries the entrywise conjugate matrices $\overline{\rho_k(g)}$. Channels are maps on matrices given by a finite normalized Kraus family. The Choi matrix is $C(\Phi)=\sum_{ij}\Phi(E_{ij})\otimes E_{ij}$, output factor first. The relation $r=m+n-2h$ is carried as the hypothesis $r+2h=m+n$. Irreducibility of $V$ is stated in the equivalent Schur form 3.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 13, Corollary 2.13 (with Lemma 2.12)

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Choi

namespace SU2Eposic.Extreme

open scoped Matrix Kronecker

/-- **Corollary 2.13, p. 13** (with Lemma 2.12). Let `m, n ∈ ℕ`, and write
`η_h = η_{m,n,h} : P_{m+n−2h} → P_m ⊗ P̄_n` and `q_h = η_h η_h*` (`= q m n h`). For every
`0 ≤ h ≤ min{m, n}`:
`η_h` is an isometry intertwining `ρ_{m+n−2h}` with `ρ_m ⊗ ρ̄_n` (so `V_{m+n−2h} = η_h(P_{m+n−2h})`
is an SU(2)-subspace isomorphic to `P_{m+n−2h}`); `q_h` is the orthogonal projection onto it
(self-adjoint and idempotent); and `V_{m+n−2h}` is irreducible: for every `T` commuting with all
`ρ_m(g) ⊗ ρ̄_n(g)`, `q_h T q_h` is a scalar multiple of `q_h`. Moreover the `q_h` are mutually
orthogonal and sum to the identity, i.e. `P_m ⊗ P̄_n = ⊕_h V_{m+n−2h}` orthogonally. -/
theorem corollary_2_13 (m n : ℕ) :
    (∀ h : ℕ, h ≤ min m n →
      (eta (m + n - 2 * h) m n h)ᴴ * eta (m + n - 2 * h) m n h = 1 ∧
      (∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        (rho m g ⊗ₖ rhoConj n g) * eta (m + n - 2 * h) m n h =
          eta (m + n - 2 * h) m n h * rho (m + n - 2 * h) g) ∧
      (q m n h)ᴴ = q m n h ∧
      q m n h * q m n h = q m n h ∧
      (∀ T : Matrix (Fin (m + 1) × Fin (n + 1)) (Fin (m + 1) × Fin (n + 1)) ℂ,
        (∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ, Commute T (rho m g ⊗ₖ rhoConj n g)) →
          ∃ μ : ℂ, q m n h * T * q m n h = μ • q m n h)) ∧
    (∀ h h' : ℕ, h ≤ min m n → h' ≤ min m n → h ≠ h' → q m n h * q m n h' = 0) ∧
    ∑ h ∈ Finset.range (min m n + 1), q m n h = 1 := by sorry

end SU2Eposic.Extreme
