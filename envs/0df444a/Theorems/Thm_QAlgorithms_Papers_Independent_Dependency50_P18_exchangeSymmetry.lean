-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_exchangeSymmetry
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.exchangeSymmetry
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:55:25.505009+00:00
-- url     : https://prove2.me/theorems/5a1714b2-2102-4ed7-a98f-57d260ff61f8
-- title:
--   Exchange symmetry
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $D$ be a dimension-compatible extended-real generalized divergence satisfying data processing for every CPTP channel, $D(r\|cs)=D(r\|s)-\log_2c$ for $c>0$, and $D(r\|r)=0$. Comparisons need not be normalized and divergence values are not truncated to be nonnegative. Write
--   $$\Gamma_D(r)=\inf_{s\ge0:\,\gamma(s)\le1}D(r\|s).$$
--
--   Let $S(|a\rangle|b\rangle)=|b\rangle|a\rangle$ be subsystem exchange. For every positive operator $s$ and every state $r$,
--   $$C_\gamma^{A:B}(s)=C_\gamma^{B:A}(SsS^\dagger),\qquad
--   \Gamma_D^{A:B}(r)=\Gamma_D^{B:A}(SrS^\dagger).$$
--
--   Both factors and subsystem labels are exchanged. This makes the measures symmetric between the two parties.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 2, Proposition 1, (6)–(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Proposition 1, PDF p.2, (6)–(7): actual subsystem exchange, including zero PSD input. -/
theorem exchangeSymmetry (D : Divergence) (hD : IsGeneralizedDivergence D) :
    (∀ sigma : Matrix (A × B) (A × B) ℂ, sigma.PosSemidef →
      cGamma sigma = cGamma (swap sigma)) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D rho = capitalGamma D (swap rho)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
