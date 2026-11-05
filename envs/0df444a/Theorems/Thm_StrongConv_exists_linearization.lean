-- Prove2me | Theorems.Thm_StrongConv_exists_linearization
-- name    : StrongConv.exists_linearization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:57:01.851843+00:00
-- url     : https://prove2.me/theorems/103f0643-f2d0-4cdf-ac31-a5827be9f9d1
-- title:
--   Lemma 9.1 — Pisier's linearization of P(s, s*) into degree-one factors
-- statement:
--   Let $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ and $\varepsilon > 0$. There are $q \ge 1$, dimensions $D_1, \dots, D_{q+1}$ with $D_1 = D_{q+1} = D$, and matrices $A_{j,i}$ of size $D_j \times D_{j+1}$ ($1 \le j \le q$, $0 \le i \le 2d$) such that, with $X_j = \sum_{i=0}^{2d} A_{j,i} \otimes \lambda(g_i)$ (where $g_0 = e$ and $g_{d+i} = g_i^{-1}$),
--   $$P(\boldsymbol s, \boldsymbol s^*) = X_1X_2\cdots X_q \quad\text{and}\quad \|X_j\| \le (\|P(\boldsymbol s, \boldsymbol s^*)\| + \varepsilon)^{1/q} \text{ for } 1 \le j \le q.$$
--   The section's polynomial is self-adjoint, but the lemma does not use that, and the statement does not assume it.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 27, Lemma 9.1 (linearization), which applies Pisier, G., On a linearization trick, Enseign. Math. 64 (2018) 315–326, Theorem 1, https://doi.org/10.4171/LEM/64-3/4-5

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem exists_linearization {D d : ℕ} (P : NCPoly D d) (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (Dim : ℕ → ℕ) (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
      (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D),
      1 ≤ q ∧ P.eval (sLimit d) = linChainOn Dim A q h₁ hq ∧
        ∀ j ∈ Finset.Icc 1 q, ‖linOp (A j)‖ ≤ (‖P.eval (sLimit d)‖ + ε) ^ (1 / (q : ℝ)) := by
  sorry

end StrongConv
