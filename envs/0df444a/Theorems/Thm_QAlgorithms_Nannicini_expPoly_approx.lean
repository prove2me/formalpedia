-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_expPoly_approx
-- name    : QAlgorithms.Nannicini.expPoly_approx
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:33.78356+00:00
-- url     : https://prove2.me/theorems/3ab4ec56-4310-460e-a1b0-8eaf67f34dec
-- title:
--   A bounded polynomial of degree Õ(β) approximating exp(2βx)/4 on [−1, 0]
-- statement:
--   There are absolute constants $C > 0$ and $c \in \mathbb{N}$ such that the following holds. Let $\xi \in (0, 1/6]$ and $\beta \ge 1$. Then there exists a real polynomial $P$ such that
--
--   1. for all $x \in [-1, 0]$, $\left|P(x) - \tfrac{1}{4} e^{2\beta x}\right| \le \xi$;
--   2. for all $x \in [-1, 1]$, $|P(x)| \le \tfrac12$;
--   3. its degree satisfies
--
--   $$
--   \deg P \le C\,\beta\,\bigl(\log(2 + \beta) + \log(2 + 1/\xi)\bigr)^{c},
--   $$
--
--   i.e. $\deg P = \widetilde{O}(\beta)$.
--
--   This polynomial approximation of the exponential on the non-positive half-interval, bounded on all of $[-1,1]$, is the ingredient that quantum singular value transformation turns into a block-encoding of $e^{\beta H}$, used to prepare Gibbs states.
--
--   **Formalization Note** The $\widetilde{O}(\beta)$ of the source (Def. 1.11, which allows polylogarithmic dependence on the other parameter $1/\xi$) is unfolded with the constants $C, c$ quantified before $\xi$ and $\beta$. The polynomial is real, since it is applied to eigenvalues of Hermitian matrices.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 171, Lemma 7.37. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch07b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Nannicini p.171, Lemma 7.37 (Lem. 4.14 in [van Apeldoorn, 2020]). Let `ξ ∈ (0, 1/6]` and
`β ≥ 1`. There is a polynomial `P` with `|P(x) − exp(2βx)/4| ≤ ξ` for all `x ∈ [−1, 0]`,
`|P(x)| ≤ 1/2` for all `x ∈ [−1, 1]`, and `deg P = Õ(β)`. The `Õ(β)` is
`C β (log(2 + β) + log(2 + 1/ξ))^c` with absolute constants `C > 0`, `c`, chosen before `ξ`, `β`
(Def. 1.11: polylogarithmic dependence on the other parameter `1/ξ` is allowed). -/
theorem expPoly_approx :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ ξ β : ℝ, 0 < ξ → ξ ≤ 1 / 6 → 1 ≤ β →
      ∃ P : Polynomial ℝ,
        (∀ x ∈ Set.Icc (-1 : ℝ) 0, |P.eval x - Real.exp (2 * β * x) / 4| ≤ ξ) ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 / 2) ∧
        (P.natDegree : ℝ) ≤ C * β * (Real.log (2 + β) + Real.log (2 + 1 / ξ)) ^ c := by
  sorry












end QAlgorithms.Nannicini
