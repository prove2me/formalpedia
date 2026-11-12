-- Prove2me | Theorems.Thm_Puder_exists_eventually_cogrowth_pow_le_sum
-- name    : Puder.exists_eventually_cogrowth_pow_le_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T14:25:33.433572+00:00
-- url     : https://prove2.me/theorems/d3cb0b2b-ec22-42cd-b912-50bef8974d38
-- title:
--   Puder, proof of Theorem 8.5 — lower half of the extended cogrowth formula on F_k's Cayley graph: ν_f(t) ≥ cα^t with α > √(2k−1) gives β_f(t) ≥ C((2k−1)/α + α)^t
-- statement:
--   Let $k \ge 2$, let $f : \mathbf F_k \to \mathbb R$ be nonnegative, and let $\alpha > \sqrt{2k-1}$ and $c > 0$. Write
--   $$\nu_f(t) = \sum_{\substack{(a_1, \dots, a_t) \\ a_{j+1} \ne a_j^{-1}}} f(a_1 \cdots a_t), \qquad \beta_f(t) = \sum_{(a_1, \dots, a_t)} f(a_1 \cdots a_t),$$
--   where the sums run over letter sequences in $g_1^{\pm 1}, \dots, g_k^{\pm 1}$ (the first over the non-backtracking ones, in which no letter is followed by its inverse) and the product is taken in $\mathbf F_k$ (`StrongConv.wordFree`). Equivalently, $\nu_f(t)$ sums $f$ over the sphere of radius $t$ and $\beta_f(t)$ over the endpoints of all walks of length $t$ from $1$ in the Cayley graph $T_{2k}$ of $\mathbf F_k$. If $c\,\alpha^t \le \nu_f(t)$ for all large $t$, then there is $C > 0$ with
--   $$C\Big(\frac{2k-1}{\alpha} + \alpha\Big)^t \le \beta_f(t) \quad \text{for all large } t.$$
--
--   This is the lower-bound counterpart of Puder's Theorem 4.4 (`Puder.limsup_sum_rpow_le_cogrowth`), for the case $\alpha > \sqrt{2k-1}$. Puder, p. 38, proof of Theorem 8.5: “If $2m - 1 > \sqrt{2k-1}$, the statement follows from the statements on reduced words (Theorems 8.2 and 8.1) and an application of the extended cogrowth formula [Pud15] (here a bit more elaborated results from [Pud15], not mentioned in Theorem 4.4, are required).” Theorem 4.4, p. 18, bounds $\limsup_{t\to\infty} \beta_f(t)^{1/t}$ by $g(\alpha)$, where (p. 17, (4.4)) “$g(\alpha) = \frac{d-1}{\alpha} + \alpha$” for “$\alpha \ge \sqrt{d-1}$”, here with $d = 2k$.
--
--   *Formalization note.* [Pud15] (“Notes on the cogrowth formula: the regular, biregular and irregular cases”, cited as a preprint) does not say which result is meant. The statement is the lower bound the proof of Theorem 8.5 needs for $f$ the indicator of $\pi(w) = m$, on the Cayley graph of $\mathbf F_k$ only.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, pp. 17–18 and 38), proof of Theorem 8.5, citing D. Puder, *Notes on the cogrowth formula: the regular, biregular and irregular cases*, preprint ([Pud15]).
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 38, proof of Theorem 8.5, the lower half of the extended cogrowth formula used for 2m − 1 > √(2k − 1), which cites Puder, D., Notes on the cogrowth formula: the regular, biregular and irregular cases, preprint ([Pud15])

import Mathlib
import Definitions.Def_StrongConv

open Filter

namespace Puder

theorem exists_eventually_cogrowth_pow_le_sum (k : ℕ) (hk : 2 ≤ k) (f : FreeGroup (Fin k) → ℝ)
    (hf : ∀ g, 0 ≤ f g) (α c : ℝ) (hα : Real.sqrt (2 * k - 1) < α) (hc : 0 < c)
    (hν : ∀ᶠ t : ℕ in atTop, c * α ^ t ≤ ∑ i : Fin t → Fin k ⊕ Fin k with
        (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap),
        f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℕ in atTop,
      C * ((2 * k - 1) / α + α) ^ t ≤ ∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j))) := by
  sorry

end Puder
