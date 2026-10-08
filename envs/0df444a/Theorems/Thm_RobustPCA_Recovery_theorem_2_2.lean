-- Prove2me | Theorems.Thm_RobustPCA_Recovery_theorem_2_2
-- name    : RobustPCA.Recovery.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:58.215984+00:00
-- url     : https://prove2.me/theorems/42153081-d65f-4317-afa7-56cf5e676b86
-- title:
--   Theorem 2.2 — elimination: exactness of PCP passes to trimmed sparse components
-- statement:
--   Let $\lambda\ge0$ and let $L_0,S_0\in\mathbb R^{n\times n}$. Suppose that Principal Component Pursuit
--   $$\text{minimize }\|L\|_*+\lambda\|S\|_1\quad\text{subject to}\quad L+S=L_0+S_0$$
--   has the unique solution $(L_0,S_0)$, and let $S_0'$ be a trimmed version of $S_0$: $\operatorname{supp}(S_0')\subseteq\operatorname{supp}(S_0)$ and $(S_0')_{ij}=(S_0)_{ij}$ whenever $(S_0')_{ij}\neq0$. Then PCP with input $L_0+S_0'$ has the unique solution $(L_0,S_0')$.
--
--   Removing gross errors cannot hurt recovery. The theorem makes success monotone in the support of the sparse component; this is what lets the paper pass between the uniform and the Bernoulli models and between random and fixed signs.
--
--   **Formalization Note** The weight $\lambda$ is assumed nonnegative, as it is throughout the paper; the proof uses $\lambda\ge0$ when it applies the triangle inequality to $\lambda\|\cdot\|_1$.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 10, Theorem 2.2 and Definition 2.1

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Theorem 2.2 (elimination), p. 10: if PCP (1.1) with input `L0 + S0` has the unique
solution `(L0, S0)` and `S0'` is a trimmed version of `S0` (Definition 2.1), then PCP with input
`L0 + S0'` has the unique solution `(L0, S0')`. The weight `lam` of (1.1) is nonnegative. -/
theorem theorem_2_2 {n : ℕ} (lam : ℝ) (L0 S0 S0' : RealMatrix n n) (hlam : 0 ≤ lam)
    (hexact : IsPCPExact lam L0 S0) (htrim : IsTrimmed S0' S0) :
    IsPCPExact lam L0 S0' := by sorry

end RobustPCA.Recovery
