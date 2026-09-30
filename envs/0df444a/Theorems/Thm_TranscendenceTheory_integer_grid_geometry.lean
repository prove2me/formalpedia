-- Prove2me | Theorems.Thm_TranscendenceTheory_integer_grid_geometry
-- name    : TranscendenceTheory.integer_grid_geometry
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T10:14:26.094733+00:00
-- url     : https://prove2.me/theorems/e135210a-c596-4253-bf76-db9e695c6896
-- title:
--   Integer-grid distinctness, lattice congruences, and half-shift regularity
-- statement:
--   Let $\Lambda$ be an additive subgroup of $\mathbb C$, regarded as a $\mathbb Z$-submodule. Suppose $\omega\in\Lambda$, the numbers $u_1,u_2,\omega$ are linearly independent over $\mathbb Q$, and
--
--   $$
--   (\mathbb Zu_1+\mathbb Zu_2)\cap\Lambda=\{0\}.
--   $$
--
--   For $m=(m_1,m_2,m_3)\in\mathbb Z^3$, put
--
--   $$
--   v(m)=m_1u_1+m_2u_2+m_3\omega.
--   $$
--
--   The map $v$ is injective, and for every $m,n\in\mathbb Z^3$,
--
--   $$
--   v(m)\in\Lambda\iff m_1=m_2=0,
--   $$
--
--   $$
--   v(m)+u_1/2\notin\Lambda,
--   $$
--
--   $$
--   v(m)-v(n)\in\Lambda\iff m_1=n_1\ \text{and}\ m_2=n_2.
--   $$
--
--   For a period lattice, these statements identify the period-direction points and establish that every half-shifted auxiliary grid consists of regular arguments of the elliptic and zeta functions. The result applies to all signed integer coordinates and does not require discreteness of $\Lambda$.
-- source:
--   Senthil Kumar K (2026), Theorem 1 geometric hypotheses; Section 5 definition of Gamma(A1,A2,A3) immediately before Lemma 7 and its shift by u1/2 in Lemma 8; Appendix equation (A.10). This isolates the elementary group-theoretic implications used by those grids and generalizes the period lattice to any Z-submodule of C. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

open WeierstrassEllipticZeta

theorem TranscendenceTheory.integer_grid_geometry
    (Λ : Submodule ℤ ℂ) (ω u₁ u₂ : ℂ)
    (hω : ω ∈ Λ)
    (h_independent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ Λ = ⊥) :
    Function.Injective (integerGridPoint u₁ u₂ ω) ∧
    (∀ m : Fin 3 → ℤ,
      integerGridPoint u₁ u₂ ω m ∈ Λ ↔ m 0 = 0 ∧ m 1 = 0) ∧
    (∀ m : Fin 3 → ℤ, integerGridPoint u₁ u₂ ω m + u₁ / 2 ∉ Λ) ∧
    (∀ m n : Fin 3 → ℤ,
      integerGridPoint u₁ u₂ ω m - integerGridPoint u₁ u₂ ω n ∈ Λ ↔
        m 0 = n 0 ∧ m 1 = n 1) := by sorry
