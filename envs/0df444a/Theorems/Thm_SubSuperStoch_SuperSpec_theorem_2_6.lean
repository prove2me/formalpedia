-- Prove2me | Theorems.Thm_SubSuperStoch_SuperSpec_theorem_2_6
-- name    : SubSuperStoch.SuperSpec.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:16.121709+00:00
-- url     : https://prove2.me/theorems/2331d90d-0c4c-49ae-87db-f917c67f34e3
-- title:
--   Theorem 2.6, p. 9 — chains into every row of sum ≥ 1 of a super-stochastic F and condition (2.5) give ρ(F) < 1
-- statement:
--   Let $F$ be an $n\times n$ super-stochastic matrix, and let
--   $$\mathcal R_1=\{s\mid\Lambda_s[F]<1\},\qquad \mathcal R_2=\{s\mid\Lambda_s[F]\ge1\}$$
--   be non-empty. Suppose that for each $k\in\mathcal R_2$ there is a non-zero element chain
--   $$\mathcal C_{i\to k}=[F]_{ki_r},\ \dots,\ [F]_{i_2i_1},\ [F]_{i_1i}$$
--   with $i\in\mathcal R_1$, $i_r\neq k,\dots,i_1\neq i_2,\ i\neq i_1$ (all listed entries non-zero), and let $|\mathcal C^*|$ be the largest number of elements among these chains. Put
--   $$\alpha_1=\max\{\Lambda_s[F]\mid\Lambda_s[F]<1\},\quad \alpha_2=\min\{[F]_{ij}>0\mid i,j=1,\dots,n\},\quad \alpha_3=\max\{\Lambda_s[F]\mid\Lambda_s[F]\ge1\}.$$
--   If the inequality
--   $$\sqrt[|\mathcal C^*|]{\alpha_3^{|\mathcal C^*|+1}-(\alpha_3-\alpha_1)\alpha_2^{|\mathcal C^*|}}<1 \tag{2.5}$$
--   holds, then
--   $$\rho(F)<1,$$
--   that is, every eigenvalue of $F$ has modulus less than one.
--
--   A super-stochastic matrix may have rows of sum larger than one and hence spectral radius larger than one in general; the theorem gives a checkable condition — chains feeding every row of sum at least one from a row of sum less than one, plus the scalar inequality (2.5) — under which $F$ is nevertheless Schur stable. The paper uses such bounds to analyse discrete-time positive and signed-network iterations whose update matrices are not sub-stochastic.
--
--   **Formalization Note** The chosen chains are given by a length function $\mathrm{len}$ on rows: for each $k\in\mathcal R_2$ there are $i\in\mathcal R_1$ and a chain from $i$ to $k$ of $\mathrm{len}(k)\ge1$ elements; $|\mathcal C^*|=C$ is the greatest value of $\mathrm{len}$ on $\mathcal R_2$ ("defined in Theorem 2.2" with $\mathcal S_1,\mathcal S_2$ read as $\mathcal R_1,\mathcal R_2$). The extrema $\alpha_1,\alpha_2,\alpha_3,C$ are values with hypotheses that they are the greatest/least elements of exactly the printed sets. The root in (2.5) is the real power $x^{1/C}$; the radicand is nonnegative under the hypotheses and $C\ge1$, so (2.5) is equivalent to $\alpha_3^{C+1}-(\alpha_3-\alpha_1)\alpha_2^{C}<1$. Eigenvalues are the spectrum of $F$ as a complex matrix. The proof on the page ends with $\rho(F)\le\sqrt[|\mathcal C^*|]{\cdots}$; the theorem itself claims only $\rho(F)<1$, which is what is stated here.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 9, Theorem 2.6 and (2.5); α₁, α₂, |C*| as in Theorem 2.2, p. 5

import Mathlib
import Definitions.Def_SubSuperStoch_SuperSpec_Setting

namespace SubSuperStoch.SuperSpec

theorem theorem_2_6 {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSuperStochastic F)
    (hR₁ : ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1) (hR₂ : ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s)
    (len : Fin n → ℕ)
    (hchain : ∀ k, 1 ≤ SubSuperStoch.SubSpec.rowSum F k → ∃ i, SubSuperStoch.SubSpec.rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ SubSuperStoch.SubSpec.IsChain F c (len k))
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1 ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (α₃ : ℝ) (hα₃ : IsGreatest {x | ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₃)
    (C : ℕ) (hC : IsGreatest {m | ∃ k, 1 ≤ SubSuperStoch.SubSpec.rowSum F k ∧ m = len k} C)
    (h25 : (α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C) ^ (1 / (C : ℝ)) < 1) :
    ∀ μ ∈ SubSuperStoch.SubSpec.specC F, ‖μ‖ < 1 := by sorry

end SubSuperStoch.SuperSpec
