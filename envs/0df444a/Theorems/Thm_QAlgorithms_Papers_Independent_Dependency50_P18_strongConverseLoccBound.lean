-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_strongConverseLoccBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.strongConverseLoccBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:04:20.486179+00:00
-- url     : https://prove2.me/theorems/f4cdc0bf-4f34-4b00-9a71-4bb2d77ed548
-- title:
--   Strong-converse LOCC randomness bound
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
--   Let $D(r\|s)=\operatorname{Tr}[r(\log_2r-\log_2s)]$ be Umegaki relative entropy, with $+\infty$ on support violations and no normalization requirement on $s$. Set $\Gamma_D(r)=\inf_{s\ge0:\gamma(s)\le1}D(r\|s)$. For every state $r_{AB}$,
--   $$R_\leftrightarrow(r)\le\widetilde R_\leftrightarrow(r)\le\Gamma_D(r).$$
--
--   This single-state quantity bounds both the ordinary and strong-converse distillation rates.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 4, Theorem 12, (48); p.1 seed headline

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Theorem 12, PDF pp.4–5, (48), chosen headline for the p.1 seed.
Both ordinary-to-strong-converse and Umegaki-Gamma bounds are retained. -/
theorem strongConverseLoccBound (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) :
    ordinaryRate true rho ≤ strongConverseRate true rho ∧
      strongConverseRate true rho ≤ capitalGamma umegaki rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
