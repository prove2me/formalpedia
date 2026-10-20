-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_continuityNearClassical
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.continuityNearClassical
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:02:28.363632+00:00
-- url     : https://prove2.me/theorems/39356179-3160-4795-b0b2-e0a894331374
-- title:
--   Continuity bound near the classical target
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   For $\alpha>1$, write $\widetilde D_\alpha(r\|s)=(\alpha-1)^{-1}\log_2\operatorname{Tr}[(s^{(1-\alpha)/(2\alpha)}r s^{(1-\alpha)/(2\alpha)})^\alpha]$, with $+\infty$ when $\operatorname{supp}r\nsubseteq\operatorname{supp}s$, and set $\widetilde\Gamma_\alpha=\Gamma_{\widetilde D_\alpha}$.
--
--   For $0\le\varepsilon<1$, the penalty is $p_\alpha(\varepsilon)=\frac{\alpha}{\alpha-1}\log_2\frac1{1-\varepsilon}$; set $p_\alpha(1)=+\infty$.
--
--   Let $d\ge1$ and let $w$ be a state on $\mathbb C^d\otimes\mathbb C^d$ with $F(\bar\Phi_d,w)\ge1-\varepsilon$, where $0\le\varepsilon\le1$, $F$ is squared fidelity, and $\bar\Phi_d=d^{-1}\sum_x|xx\rangle\langle xx|$. For every $\alpha>1$,
--   $$\log_2d\le\widetilde\Gamma_\alpha(w)+p_\alpha(\varepsilon).$$
--
--   This converts fidelity to the ideal mixed target into a lower bound on the correlation measure.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 3, Proposition 10, (25)–(26)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Proposition 10, PDF p.3, (25)–(26), Appendix H p.11.
The coefficient is alpha/(alpha-1), and epsilon=1 has infinite penalty. -/
theorem continuityNearClassical (d : ℕ) (hd : 0 < d)
    (omega : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (homega : QAlgorithms.IsDensityMatrix omega) (eps alpha : ℝ)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) (halpha : 1 < alpha)
    (hfid : 1 - eps ≤ QAlgorithms.Papers.Independent.Information100.P67.squaredFidelity (classicalTarget d) omega) :
    (Real.logb 2 d : EReal) ≤ capitalGamma (sandwiched alpha) omega +
      errorPenalty alpha eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
