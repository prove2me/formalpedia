-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_fixedMarginalComparison
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.fixedMarginalComparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:06:09.56153+00:00
-- url     : https://prove2.me/theorems/8fa4dd35-3226-4595-8838-a1687352e380
-- title:
--   Fixed-marginal semidefinite comparisons
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $D$ be a dimension-compatible extended-real generalized divergence satisfying data processing for every CPTP channel, $D(r\|cs)=D(r\|s)-\log_2c$ for $c>0$, and $D(r\|r)=0$. Comparisons need not be normalized and divergence values are not truncated to be nonnegative. Write
--   $$\Gamma_D(r)=\inf_{s\ge0:\,\gamma(s)\le1}D(r\|s).$$
--
--   For a fixed local state $a_A$, let $\beta_A(s,a)$ be the same extended trace infimum as $\gamma(s)$ with $K_A=a_A$ fixed. Define $\beta_B(s,b)$ by fixing $L_B=b_B$ instead. Thus all Hermitian requirements and both signs of both PSD constraints remain. For a target state $r$, let $r_A=\operatorname{Tr}_B r$ and $r_B=\operatorname{Tr}_A r$, and define
--   $$\Upsilon^A_D(r)=\inf_{s\ge0:\,\beta_A(s,r_A)\le1}D(r\|s),\qquad
--   \Upsilon^B_D(r)=\inf_{s\ge0:\,\beta_B(s,r_B)\le1}D(r\|s).$$
--
--   The references are fixed target marginals, not marginals of the optimized comparison.
--
--   For every positive $s$, every local state $a$ on Alice, and every local state $b$ on Bob,
--   $$\gamma(s)\le\beta_A(s,a),\qquad \gamma(s)\le\beta_B(s,b).$$
--
--   For every target state $r$,
--   $$\Gamma_D(r)\le\min\{\Upsilon^A_D(r),\Upsilon^B_D(r)\}.$$
--
--   The restricted infima may be infinite for singular references. These comparisons replace a bilinear optimization by either independent fixed-marginal restriction.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 5, VI, (52)–(55)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Section VI, PDF p.5, (52)–(55): both restrictions and the minimum comparison. -/
theorem fixedMarginalComparison (D : Divergence) (hD : IsGeneralizedDivergence D) :
    (∀ (sigma : Matrix (A × B) (A × B) ℂ) (a : Matrix A A ℂ),
      sigma.PosSemidef → QAlgorithms.IsDensityMatrix a → correlationGauge sigma ≤ betaA sigma a) ∧
    (∀ (sigma : Matrix (A × B) (A × B) ℂ) (b : Matrix B B ℂ),
      sigma.PosSemidef → QAlgorithms.IsDensityMatrix b → correlationGauge sigma ≤ betaB sigma b) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D rho ≤ min (upsilonA D rho) (upsilonB D rho)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
