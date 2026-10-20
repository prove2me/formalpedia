-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_nonnegativityAndFaithfulness
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.nonnegativityAndFaithfulness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:57:45.14998+00:00
-- url     : https://prove2.me/theorems/3cd04078-b565-4457-aab9-b6273d58096b
-- title:
--   Nonnegativity and faithfulness
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $D$ be a dimension-compatible extended-real generalized divergence satisfying data processing for every CPTP channel, $D(r\|cs)=D(r\|s)-\log_2c$ for $c>0$, and $D(r\|r)=0$. Comparisons need not be normalized and divergence values are not truncated to be nonnegative. Write
--   $$\Gamma_D(r)=\inf_{s\ge0:\,\gamma(s)\le1}D(r\|s).$$
--
--   For every state $r_{AB}$ satisfying the additional boundary condition $D(r_{AB}\|0)\ge0$,
--   $$C_\gamma(r)\ge0,\qquad \Gamma_D(r)\ge0.$$
--
--   Both quantities vanish if $r=s_A\otimes t_B$ for local states $s_A,t_B$. Conversely, $C_\gamma(r)=0$ implies that $r$ is such a product state. If, additionally, $D$ is faithful on pairs of normalized states and lower semicontinuous in its PSD second argument, then $\Gamma_D(r)=0$ also implies that $r$ is a product state. Faithfulness means $D(u\|v)=0$ if and only if $u=v$ for states $u,v$; it does not impose nonnegativity on supernormalized comparisons.
--
--   These clauses identify when the measures detect correlations.
--
--   Source correction: the printed three axioms leave the zero comparison open. The added condition is necessary because the zero comparison is feasible in the defining infimum; no positivity assumption is imposed on other nonnormalized comparisons.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 3, Proposition 4, (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Proposition 4, PDF p.3, (14), Appendix C pp.8–9: every clause is retained.
Printed: the three Section II laws suffice, without a zero-comparison condition.
Changed: assume only `0 ≤ D rho 0` for this input state. Why: the printed laws allow
D(rho||0)=-infinity, and zero is feasible in (4), contradicting nonnegativity.
This is the necessary boundary condition, not positivity on arbitrary comparisons;
Umegaki and sandwiched divergences satisfy it. Independent moderation is required.
Faithfulness and lower semicontinuity of D are premises only of the final implication. -/
theorem nonnegativityAndFaithfulness (D : Divergence) (hD : IsGeneralizedDivergence D)
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hzeroComparison : 0 ≤ D rho 0) :
    0 ≤ cGamma rho ∧ 0 ≤ capitalGamma D rho ∧
    (IsProductState rho → cGamma rho = 0 ∧ capitalGamma D rho = 0) ∧
    (cGamma rho = 0 → IsProductState rho) ∧
    (DivergenceFaithful D → DivergenceLowerSemicontinuous D →
      capitalGamma D rho = 0 → IsProductState rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
