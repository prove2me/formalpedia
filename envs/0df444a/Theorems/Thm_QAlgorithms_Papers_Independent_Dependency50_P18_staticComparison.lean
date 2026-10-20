-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_staticComparison
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.staticComparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:07:32.46778+00:00
-- url     : https://prove2.me/theorems/44656997-f69e-4c5c-864b-25eaf09e7dfa
-- title:
--   Comparison with static beta and Upsilon
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
--   Define the distinct static quantities $\beta_{\rm st}(s)=\beta_A(s,\operatorname{Tr}_B s)$ and $\Upsilon_{\rm st,D}(r)=\inf_{s\ge0:\beta_{\rm st}(s)\le1}D(r\|s)$. Thus the static reference is the comparison operator's own marginal and may be unnormalized. For every positive $s$ and every state $r$,
--   $$\gamma(s)\le\beta_{\rm st}(s),\qquad \Gamma_D(r)\le\Upsilon_{\rm st,D}(r).$$
--
--   These compare the new symmetric quantities with the separate static restrictions from Appendix I, without identifying them with either target-marginal Upsilon.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 11, Appendix I, (184)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Appendix I, PDF p.11, (184): static beta fixes the comparison's own marginal. -/
theorem staticComparison (D : Divergence) (hD : IsGeneralizedDivergence D) :
    (∀ sigma : Matrix (A × B) (A × B) ℂ, sigma.PosSemidef → correlationGauge sigma ≤ staticBeta sigma) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D rho ≤ staticUpsilon D rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
