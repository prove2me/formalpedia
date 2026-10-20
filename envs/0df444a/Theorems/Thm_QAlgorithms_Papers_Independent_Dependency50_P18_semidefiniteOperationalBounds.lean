-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_semidefiniteOperationalBounds
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.semidefiniteOperationalBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:06:51.201045+00:00
-- url     : https://prove2.me/theorems/649404b0-935f-42cd-8fdd-a747e663570a
-- title:
--   Semidefinite operational upper bounds
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   For a state $r_{AB}$, let $R^\varepsilon_\to(r)$ and $R^\varepsilon_\leftrightarrow(r)$ be the suprema of $\log_2d-\sum_i\log_2|L_i|$ over, respectively, Alice-to-Bob and arbitrary finite-round LOCC protocols. Each protocol uses local CPTP operations, finite classical messages $L_i$, arbitrary finite local memories, and no free shared seed. Its final classical state $w$ must satisfy $F(w,\bar\Phi_d)\ge1-\varepsilon$, where $F$ is squared fidelity and $\bar\Phi_d=d^{-1}\sum_{x=0}^{d-1}|xx\rangle\langle xx|$. Every alphabet size and $d$ is positive; unused symbols still contribute to the communication charge.
--
--   For either direction convention $b\in\{\to,\leftrightarrow\}$, define
--   $$R_b(r)=\inf_{0<\varepsilon\le1}\liminf_{n\to\infty}\frac1nR_b^\varepsilon(r^{\otimes n}),\qquad
--   \widetilde R_b(r)=\sup_{0\le\varepsilon<1}\limsup_{n\to\infty}\frac1nR_b^\varepsilon(r^{\otimes n}),$$
--   where block lengths start at one and tensor powers are constructed from the given state.
--
--   For a fixed local state $a_A$, let $\beta_A(s,a)$ be the same extended trace infimum as $\gamma(s)$ with $K_A=a_A$ fixed. Define $\beta_B(s,b)$ by fixing $L_B=b_B$ instead. Thus all Hermitian requirements and both signs of both PSD constraints remain. For a target state $r$, let $r_A=\operatorname{Tr}_B r$ and $r_B=\operatorname{Tr}_A r$, and define
--   $$\Upsilon^A_D(r)=\inf_{s\ge0:\,\beta_A(s,r_A)\le1}D(r\|s),\qquad
--   \Upsilon^B_D(r)=\inf_{s\ge0:\,\beta_B(s,r_B)\le1}D(r\|s).$$
--
--   The references are fixed target marginals, not marginals of the optimized comparison.
--
--   For $\alpha>1$, write $\widetilde D_\alpha(r\|s)=(\alpha-1)^{-1}\log_2\operatorname{Tr}[(s^{(1-\alpha)/(2\alpha)}r s^{(1-\alpha)/(2\alpha)})^\alpha]$, with $+\infty$ when $\operatorname{supp}r\nsubseteq\operatorname{supp}s$, and set $\widetilde\Gamma_\alpha=\Gamma_{\widetilde D_\alpha}$.
--
--   For $0\le\varepsilon<1$, the penalty is $p_\alpha(\varepsilon)=\frac{\alpha}{\alpha-1}\log_2\frac1{1-\varepsilon}$; set $p_\alpha(1)=+\infty$.
--
--   Use $D$ equal to bit-valued support-aware Umegaki divergence in the rate bound, and $\widetilde D_\alpha$ in the one-shot bound. For every state $r$, $0\le\varepsilon\le1$, and $\alpha>1$,
--   $$R^\varepsilon_\leftrightarrow(r)\le
--   \min\{\Upsilon^A_{\widetilde D_\alpha}(r),\Upsilon^B_{\widetilde D_\alpha}(r)\}+p_\alpha(\varepsilon),$$
--   $$\widetilde R_\leftrightarrow(r)\le\min\{\Upsilon^A_D(r),\Upsilon^B_D(r)\}.$$
--
--   Each minimum compares two independently restricted optimizations; no equality or tightness is claimed. These give semidefinite restrictions of the operational converse bounds.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 5, VI, (56)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Section VI, PDF p.5, (56): both one-shot and strong-converse semidefinite
bounds. The PDF prints alpha'=alpha/(alpha-1); the extraction inverted it. -/
theorem semidefiniteOperationalBounds (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (eps alpha : ℝ)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) (halpha : 1 < alpha) :
    oneShot true eps rho ≤ min (upsilonA (sandwiched alpha) rho)
      (upsilonB (sandwiched alpha) rho) + errorPenalty alpha eps ∧
    strongConverseRate true rho ≤ min (upsilonA umegaki rho) (upsilonB umegaki rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
