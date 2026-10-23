-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_classicalFidelityBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.classicalFidelityBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:01:36.383796+00:00
-- url     : https://prove2.me/theorems/4bad2e9b-ab71-4bc1-b8dd-52c11ad25e1b
-- title:
--   Fidelity ceiling for the classical target
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $d\ge1$, let $A=B=\mathbb C^d$, and let $\bar\Phi_d=d^{-1}\sum_{x=0}^{d-1}|xx\rangle\langle xx|$, a separable diagonal mixed state. For every $s\ge0$ with $\gamma(s)\le1$,
--   $$F(\bar\Phi_d,s)\le\frac1d,\qquad F(u,v)=\|\sqrt u\sqrt v\|_1^2.$$
--
--   Equivalently, the supremum over these comparisons is at most $1/d$. Comparisons need not have trace one. This separates the desired classical target from the comparison set.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 3, Lemma 9, (22)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Lemma 9, PDF p.3, (22), Appendix G pp.10–11: equivalent universal formulation
of the supremum bound, with no trace-one condition on the comparison. -/
theorem classicalFidelityBound (d : ℕ) (hd : 0 < d)
    (sigma : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hsigma : sigma.PosSemidef) (hgamma : correlationGauge sigma ≤ 1) :
    QAlgorithms.Papers.Independent.Information100.P67.squaredFidelity (classicalTarget d) sigma ≤ 1 / (d : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
