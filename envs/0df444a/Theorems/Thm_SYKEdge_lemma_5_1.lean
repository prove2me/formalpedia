-- Prove2me | Theorems.Thm_SYKEdge_lemma_5_1
-- name    : SYKEdge.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:50.451307+00:00
-- url     : https://prove2.me/theorems/33eb5ebf-10f3-4817-b5ba-b3651979d6bc
-- title:
--   Lemma 5.1 — sign matrix eigenvalues: $\lambda_j\approx(-2)^j\binom{n-2j}{k-j}\binom nk^{-1}$ within $8\alpha$, sign pattern, $|\lambda_1|\approx2k/n$, $2\alpha-2\alpha^2\le1-\lambda_0\le2\alpha$
-- statement:
--   Suppose $n\ge k\ge2$, write $\alpha=k^2/n$ and assume $\alpha<1/16$. For $\lambda_j$ as in (27):
--   $$\left|\frac{\lambda_j}{(-2)^j\binom{n-2j}{k-j}\binom nk^{-1}}-1\right|\le8\alpha\qquad(0\le j\le k),\qquad(29)$$
--   in particular $\lambda_j>0$ if and only if $j$ is even. Moreover:
--
--   1. $(1-k/n)(1-8\alpha)\le|\lambda_1|/(2k/n)\le1+8\alpha$;
--   2. $|\lambda_j|\le2(8k/n)^j$ for all $j\ge0$, and consequently $\sum_{j=0}^kd_j|\lambda_j|\le e^{9k}$, where $d_j=\binom nj-\binom n{j-1}$;
--   3. $\max_{2\le j\le k,\ j\text{ even}}\lambda_j=\Theta(\alpha/n)$;
--   4. $\max_{1\le j\le k,\ j\text{ odd}}|\lambda_j|=|\lambda_1|\le(2+O(\alpha))\sqrt{\alpha/n}$;
--   5. $2\alpha-2\alpha^2\le1-\lambda_0\le2\alpha$.
--
--   Here $\Theta$ and $O$ hide absolute constants. Through (28), item 5 gives $1-q\approx2\alpha$ and items 3–4 give $\rho^+=O(\alpha/n)$ and $\rho^-=O(\sqrt{\alpha/n})$, the inputs of Theorems 5.2 and 5.3.
--
--   **Formalization Note** The constants of $\Theta(\alpha/n)$ and $O(\alpha)$ are absolute and are chosen before $n,k$. A maximum over a finite nonempty range is stated by bounding every term, and (for the lower bound of item 3) exhibiting a term that reaches the bound.
--
--   Differences from the source:
--   - encoding: Θ(α/n) and O(α) → absolute constants c₃, C₃, C₄ > 0 quantified before n, k; reason: asymptotic notation in the paper hides absolute constants
--   - encoding: max_{2⩽j⩽k, j even} λ_j = Θ(α/n); max_{1⩽j⩽k, j odd} |λ_j| = |λ_1| → ∃ even j ∈ [2,k] with λ_j ⩾ c₃α/n and every even λ_j ⩽ C₃α/n; every odd |λ_j| ⩽ |λ_1|; reason: the maximum of a finite nonempty family is the attained upper bound; j = 1 is odd
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 5.1, p.34

import Mathlib
import Definitions.Def_SYKEdge_Johnson

namespace SYKEdge

/-- **Lemma 5.1** (Sign Matrix Eigenvalues), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.34.

Suppose `n ⩾ k ⩾ 2`, `α := k²/n < 1/16`. For `λ_j` as in (27):
`|λ_j / ((−2)^j (n−2j choose k−j)(n choose k)^{−1}) − 1| ⩽ 8α` (29); in particular `λ_j > 0` iff `j` is
even. Moreover
(1) `(1 − k/n)(1 − 8α) ⩽ |λ₁|/(2k/n) ⩽ 1 + 8α`;
(2) `|λ_j| ⩽ 2(8k/n)^j` for all `j ⩾ 0`, and consequently `Σ_{j=0}^{k} d_j |λ_j| ⩽ e^{9k}`;
(3) `max_{2⩽j⩽k, j even} λ_j = Θ(α/n)`;
(4) `max_{1⩽j⩽k, j odd} |λ_j| = |λ₁| ⩽ (2 + O(α))·√(α/n)`;
(5) `2α − 2α² ⩽ 1 − λ₀ ⩽ 2α`.

**Formalization Note.** `Θ(α/n)` and `O(α)` are absolute constants `c₃, C₃, C₄ > 0`, chosen before
`n, k`. A maximum over a finite nonempty index set is stated as a bound by every term together with
(for the lower bound of (3)) a term that reaches it; `max_{odd} |λ_j| = |λ₁|` is "every odd `|λ_j|` is
at most `|λ₁|`" (`j = 1` is odd). (29) and the sign pattern are for `0 ⩽ j ⩽ k`, where (27) defines
`λ_j`; (2)'s first bound is for every `j ∈ ℕ` (for `j > k`, `λ_j = 0`). -/
theorem lemma_5_1 :
    ∃ c₃ C₃ C₄ : ℝ, 0 < c₃ ∧ 0 < C₃ ∧ 0 < C₄ ∧
    ∀ n k : ℕ, 2 ≤ k → k ≤ n → (k : ℝ) ^ 2 / n < 1 / 16 →
      (∀ j ≤ k, |lamJ n k j /
          ((-2 : ℝ) ^ j * (((n - 2 * j).choose (k - j) : ℕ) : ℝ) / ((n.choose k : ℕ) : ℝ)) - 1|
          ≤ 8 * ((k : ℝ) ^ 2 / n)) ∧
      (∀ j ≤ k, 0 < lamJ n k j ↔ Even j) ∧
      ((1 - (k : ℝ) / n) * (1 - 8 * ((k : ℝ) ^ 2 / n)) ≤ |lamJ n k 1| / (2 * k / n) ∧
        |lamJ n k 1| / (2 * k / n) ≤ 1 + 8 * ((k : ℝ) ^ 2 / n)) ∧
      (∀ j : ℕ, |lamJ n k j| ≤ 2 * (8 * (k : ℝ) / n) ^ j) ∧
      (∑ j ∈ Finset.range (k + 1), ((dJ n j : ℕ) : ℝ) * |lamJ n k j| ≤ Real.exp (9 * k)) ∧
      (∃ j, 2 ≤ j ∧ j ≤ k ∧ Even j ∧ c₃ * ((k : ℝ) ^ 2 / n) / n ≤ lamJ n k j) ∧
      (∀ j, 2 ≤ j → j ≤ k → Even j → lamJ n k j ≤ C₃ * ((k : ℝ) ^ 2 / n) / n) ∧
      (∀ j, 1 ≤ j → j ≤ k → Odd j → |lamJ n k j| ≤ |lamJ n k 1|) ∧
      |lamJ n k 1| ≤ (2 + C₄ * ((k : ℝ) ^ 2 / n)) * Real.sqrt (((k : ℝ) ^ 2 / n) / n) ∧
      (2 * ((k : ℝ) ^ 2 / n) - 2 * ((k : ℝ) ^ 2 / n) ^ 2 ≤ 1 - lamJ n k 0 ∧
        1 - lamJ n k 0 ≤ 2 * ((k : ℝ) ^ 2 / n)) := by sorry

end SYKEdge
