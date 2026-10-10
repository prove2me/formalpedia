-- Prove2me | Theorems.Thm_SubSuperStoch_SubSpec_theorem_2_2
-- name    : SubSuperStoch.SubSpec.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:31.61706+00:00
-- url     : https://prove2.me/theorems/ab0e344c-40fe-440e-9dff-6162f975fcea
-- title:
--   Theorem 2.2, pp. 4–5 — chains to the unit rows give ρ(F) ≤ (1 − (1 − α₁)α₂^{|C*|})^{1/(|C*|+1)} < 1
-- statement:
--   Let $F$ be an $n\times n$ sub-stochastic matrix: $[F]_{ij}\ge 0$ and $\Lambda_i[F]=\sum_j [F]_{ij}\le 1$ for all $i$. Let
--   $$\mathcal S_1=\{s\mid\Lambda_s[F]<1\},\qquad \mathcal S_2=\{s\mid\Lambda_s[F]=1\}$$
--   be non-empty. Suppose that for each $k\in\mathcal S_2$ there is a non-zero element chain
--   $$\mathcal C_{i\to k}:\ [F]_{k i_r},\ \dots,\ [F]_{i_2 i_1},\ [F]_{i_1 i},\qquad i\in\mathcal S_1,\ i_r\ne k,\ \dots,\ i_1\ne i_2,\ i\ne i_1,$$
--   whose entries are all non-zero. Put
--   $$\alpha_1=\max\{\Lambda_s[F]\mid\Lambda_s[F]<1\},\quad \alpha_2=\min\{[F]_{ij}>0\mid i,j=1,\dots,n\},\quad |\mathcal C^*|=\max\{|\mathcal C_{i\to k}|\mid i\in\mathcal S_1,\ k\in\mathcal S_2\},$$
--   where $|\mathcal C_{i\to k}|$ is the number of elements of $\mathcal C_{i\to k}$. Then the spectral radius of $F$ satisfies
--   $$\rho(F)\le\sqrt[|\mathcal C^*|+1]{1-(1-\alpha_1)\alpha_2^{|\mathcal C^*|}}<1. \tag{2.1}$$
--
--   The theorem gives a checkable sufficient condition for a sub-stochastic matrix to be strictly stable, $\rho(F)<1$, with an explicit bound: it suffices that every row of sum one can be reached by a chain of non-zero entries from a row of sum less than one. It is the matrix tool behind the convergence results for asynchronous bipartite tracking in the same paper.
--
--   **Formalization Note** Indices are 0-based. The chain for $k\in\mathcal S_2$ is a function `c` with `c 0 = i ∈ S₁`, `c (len k) = k`, `1 ≤ len k`, entries `F (c (t+1)) (c t) ≠ 0` and `c (t+1) ≠ c t`; the hypothesis provides one chain per $k$, of length `len k`, and $|\mathcal C^*|$ is the largest of these chosen lengths (`IsGreatest {m | ∃ k, rowSum F k = 1 ∧ m = len k} C`). $\alpha_1$ and $\alpha_2$ are passed as values with `IsGreatest`/`IsLeast` hypotheses over exactly the printed sets. $\rho(F)\le b$ is stated for every complex eigenvalue (`specC F`), and the root is the real power $x^{1/(|\mathcal C^*|+1)}$; its radicand lies in $(0,1)$.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, pp. 4–5, Theorem 2.2 and (2.1)

import Mathlib
import Definitions.Def_SubSuperStoch_SubSpec_Setting

namespace SubSuperStoch.SubSpec

theorem theorem_2_2 {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
    (hS₁ : ∃ s, rowSum F s < 1) (hS₂ : ∃ s, rowSum F s = 1)
    (len : Fin n → ℕ)
    (hchain : ∀ k, rowSum F k = 1 → ∃ i, rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ IsChain F c (len k))
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (C : ℕ) (hC : IsGreatest {m | ∃ k, rowSum F k = 1 ∧ m = len k} C) :
    (∀ μ ∈ specC F, ‖μ‖ ≤ (1 - (1 - α₁) * α₂ ^ C) ^ (1 / ((C : ℝ) + 1))) ∧
      (1 - (1 - α₁) * α₂ ^ C) ^ (1 / ((C : ℝ) + 1)) < 1 := by sorry

end SubSuperStoch.SubSpec
