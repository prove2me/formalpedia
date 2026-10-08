-- Prove2me | Theorems.Thm_TensorNP_SymEigen_theorem_9_3_core
-- name    : TensorNP.SymEigen.theorem_9_3_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:39.187003+00:00
-- url     : https://prove2.me/theorems/a9b36b48-e00b-40d2-b41b-4f7076f62ca2
-- title:
--   Theorem 9.3 (core) — α(G) is the largest l ≤ v for which 2√(⅔(1 − 1/l)) is an ℓ²-eigenvalue of S_G
-- statement:
--   Let $G$ be a simple graph on $v\ge1$ vertices with stability number $\alpha(G)$, let $\mathcal S_G$ be its symmetric tensor from §9, and for $l\ge1$ let $\lambda_l=2\sqrt{\frac23\left(1-\frac1l\right)}$. Then $\alpha(G)$ is the greatest element of
--   $$\{\,l\in\{1,\dots,v\}:\ \lambda_l\text{ is a unit }\ell^2\text{-eigenvalue of }\mathcal S_G\,\}.$$
--   Equivalently: (a) $\lambda_{\alpha(G)}$ is an $\ell^2$-eigenvalue of $\mathcal S_G$, and (b) for every $l$ with $\alpha(G)<l\le v$, $\lambda_l$ is not.
--
--   This is the mathematical core of Hillar and Lim's proof that symmetric tensor eigenvalue over $\mathbb R$ is NP-hard (Theorem 9.3): querying an oracle for Problem 9.1 with $\lambda_v,\lambda_{v-1},\dots,\lambda_1$, the first "yes" occurs at $l=\alpha(G)$, so at most $v$ queries compute the stability number, which is NP-hard (Karp 1972, via $\alpha(G)=\omega(\overline G)$).
--
--   **Formalization Note** Only the characterization is formalized. The oracle procedure, the polynomial size of $\mathcal S_G$, the input model with quadratic irrationalities $\lambda_l$ (Remark 9.4), and the NP-completeness of the stability number are not. Eigenvalues are taken with a unit eigenvector; with the paper's bare condition $\mathbf x\neq\mathbf 0$, part (b) would be false by scaling.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:28, Theorem 9.3 and its proof; Problem 9.1, p. 0:27

import Mathlib
import Definitions.Def_TensorNP_SymEigen_Defs
import Definitions.Def_TensorNP_SymEigen_StabTensor

namespace TensorNP.SymEigen

theorem theorem_9_3_core {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) :
    IsGreatest {l : ℕ | 1 ≤ l ∧ l ≤ v ∧ IsUnitL2Eigenvalue (stabTensor G) (lambdaL l)}
      G.indepNum := by sorry

end TensorNP.SymEigen
