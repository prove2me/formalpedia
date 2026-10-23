-- Prove2me | Theorems.Thm_PermInvConvex_Sparsity_proposition_3_4
-- name    : PermInvConvex.Sparsity.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:57.270239+00:00
-- url     : https://prove2.me/theorems/3d8c6684-7a57-4ca9-932b-3cb515934ecc
-- title:
--   Proposition 3.4, p. 8 — recursion for s(x), unimodality, u(x) ≥m |x|, and u(x)₁ = max{|x|[1], s(x)₁}
-- statement:
--   Let $1 < K < n$, $x \in \mathbb R^n$, and let $s(x)$, $i_x$, $\delta(x)$ and $u(x)$ be as in (15). Then:
--
--   1. for $i = 1, \dots, K-1$,
--   $$s(x)_{i+1} - s(x)_i = \frac{1}{K-i+1}\big(s(x)_{i+1} - |x|_{[i]}\big) = \frac{1}{K-i}\big(s(x)_i - |x|_{[i]}\big);$$
--   2. $s(x)_1 \ge \dots \ge s(x)_{i_x}$ and $s(x)_{i_x} \le \dots \le s(x)_K$;
--   3. $u(x) \ge_m |x|$;
--   4. $u(x)_1 = \max\{|x|_{[1]}, s(x)_1\}$.
--
--   Part 3 is the input to the inequality $\|x\|_c \le \|u(x)\|_s$ of Theorem 3.1, and Part 2 says the sequence $s(x)$ is unimodal with its first minimum at $i_x$.
--
--   **Formalization Note** $|x|_{[i]}$ with the paper's 1-based $i$ is `decAbs x ⟨i - 1, _⟩`, and $u(x)_1$ is the Lean coordinate `0`. Part 2 is stated as two monotonicity statements on the integer ranges $1 \le i \le j \le i_x$ and $i_x \le i \le j \le K$. No norm is involved; $1 < K < n$ is the standing assumption of §3 (p. 6).
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 8, Proposition 3.4 (definitions on p. 7; standing assumption 1 < K < n, p. 6)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

namespace PermInvConvex.Sparsity

theorem proposition_3_4 {n : ℕ} (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) :
    (∀ (i : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K - 1),
        sVal K x (i + 1) - sVal K x i =
            1 / ((K : ℝ) - i + 1) * (sVal K x (i + 1) - decAbs x ⟨i - 1, by omega⟩) ∧
          sVal K x (i + 1) - sVal K x i =
            1 / ((K : ℝ) - i) * (sVal K x i - decAbs x ⟨i - 1, by omega⟩)) ∧
    ((∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ ix K x → sVal K x j ≤ sVal K x i) ∧
      (∀ i j : ℕ, ix K x ≤ i → i ≤ j → j ≤ K → sVal K x i ≤ sVal K x j)) ∧
    Majorizes (uVec K x) (absVec x) ∧
    uVec K x ⟨0, by omega⟩ = max (decAbs x ⟨0, by omega⟩) (sVal K x 1) := by sorry

end PermInvConvex.Sparsity
