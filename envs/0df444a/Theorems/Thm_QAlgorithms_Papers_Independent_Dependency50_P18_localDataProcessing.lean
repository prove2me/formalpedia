-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_localDataProcessing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.localDataProcessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:56:11.835419+00:00
-- url     : https://prove2.me/theorems/587ccb8c-4290-41fd-a797-499189efe409
-- title:
--   Data processing under local channels
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $D$ be a dimension-compatible extended-real generalized divergence satisfying data processing for every CPTP channel, $D(r\|cs)=D(r\|s)-\log_2c$ for $c>0$, and $D(r\|r)=0$. Comparisons need not be normalized and divergence values are not truncated to be nonnegative. Write
--   $$\Gamma_D(r)=\inf_{s\ge0:\,\gamma(s)\le1}D(r\|s).$$
--
--   For local CPTP channels $N:A\to A'$ and $M:B\to B'$, every positive operator $s$ and every state $r$ satisfy
--   $$C_\gamma((N\otimes M)(s))\le C_\gamma(s),\qquad
--   \Gamma_D((N\otimes M)(r))\le\Gamma_D(r).$$
--
--   Each output is formed from its own input. The measures therefore cannot increase under local processing.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 2, Proposition 2, (8)–(9)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Proposition 2, PDF p.2, (8)–(9), Appendix B pp.7–8.
The printed sigma/rho mismatch is corrected as in Appendix B: C_gamma has PSD input,
Gamma has normalized input, and each output is computed from its own input. -/
theorem localDataProcessing (D : Divergence) (hD : IsGeneralizedDivergence D)
    (N : QAlgorithms.Superop A C) (M : QAlgorithms.Superop B E)
    (hN : QAlgorithms.IsChannel N) (hM : QAlgorithms.IsChannel M) :
    (∀ sigma : Matrix (A × B) (A × B) ℂ, sigma.PosSemidef →
      cGamma (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M sigma) ≤ cGamma sigma) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M rho) ≤ capitalGamma D rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
