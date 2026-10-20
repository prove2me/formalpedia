-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_subadditivity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.subadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:00:57.205754+00:00
-- url     : https://prove2.me/theorems/c7cba474-c5fe-4f73-99f7-086f985b1856
-- title:
--   Subadditivity on product inputs
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $D$ be a dimension-compatible extended-real generalized divergence satisfying data processing for every CPTP channel, $D(r\|cs)=D(r\|s)-\log_2c$ for $c>0$, and $D(r\|r)=0$. Comparisons need not be normalized and divergence values are not truncated to be nonnegative. Write
--   $$\Gamma_D(r)=\inf_{s\ge0:\,\gamma(s)\le1}D(r\|s).$$
--
--   For positive operators $s_{A_1B_1},t_{A_2B_2}$, construct $r=s\otimes t$ and regroup its systems into $A_1A_2:B_1B_2$. Then
--   $$C_\gamma^{A_1A_2:B_1B_2}(r)\le C_\gamma^{A_1:B_1}(s)+C_\gamma^{A_2:B_2}(t).$$
--
--   If $D(u\otimes v\|s\otimes t)\le D(u\|s)+D(v\|t)$ for states $u,v$ and positive comparisons $s,t$, then, for normalized factors $s,t$,
--   $$\Gamma_D^{A_1A_2:B_1B_2}(s\otimes t)\le\Gamma_D^{A_1:B_1}(s)+\Gamma_D^{A_2:B_2}(t).$$
--
--   Only the second clause needs the additional divergence premise. This controls tensor-product accumulation without asserting additivity.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 3, Proposition 8, (20)–(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Proposition 8, PDF p.3, (20)–(21), Appendix F p.10.
Only the Gamma clause requires subadditivity of D; the product input is constructed. -/
theorem subadditivity (D : Divergence) (hD : IsGeneralizedDivergence D) :
    (∀ (sigma : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × E) (C × E) ℂ),
      sigma.PosSemidef → tau.PosSemidef →
      cGamma (bipartiteTensor sigma tau) ≤ cGamma sigma + cGamma tau) ∧
    (DivergenceSubadditive D →
      ∀ (sigma : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × E) (C × E) ℂ),
      QAlgorithms.IsDensityMatrix sigma → QAlgorithms.IsDensityMatrix tau →
      capitalGamma D (bipartiteTensor sigma tau) ≤ capitalGamma D sigma + capitalGamma D tau) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
