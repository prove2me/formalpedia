-- Prove2me | Theorems.Thm_Puder_limsup_sum_rpow_le_cogrowth
-- name    : Puder.limsup_sum_rpow_le_cogrowth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T10:16:23.39456+00:00
-- url     : https://prove2.me/theorems/9a661b20-6057-49f7-afc8-ee9df543c368
-- title:
--   Puder, Theorem 4.4 — Extended cogrowth formula on the Cayley graph of F_k: ν_f(t) ≤ cα^t ⇒ limsup β_f(t)^{1/t} ≤ g(α)
-- statement:
--   Let $k \ge 2$ and let $f : \mathbf F_k \to \mathbb R$ be nonnegative, a function on the vertices of the Cayley graph of $\mathbf F_k$ with respect to $g_1, \dots, g_k$, which is the $2k$-regular tree based at $1$. Write the $2k$ letters as $g_i$ and $g_i^{-1}$ (`Fin k ⊕ Fin k`, with `Sum.inl i` for $g_i$, `Sum.inr i` for $g_i^{-1}$, and `Sum.swap` taking a letter to its inverse). A word of length $t$ in the letters is a walk of length $t$ from $1$, ending at its product in $\mathbf F_k$ (the word is `List.ofFn` of the letters, reduced by `StrongConv.wordFree`); it is non-backtracking when no letter is immediately followed by its inverse. Let
--   $$\beta_f(t) = \sum_{\text{words } w \text{ of length } t} f(w), \qquad \nu_f(t) = \sum_{\text{non-backtracking words } w \text{ of length } t} f(w).$$
--   Let $\alpha \ge 0$ and $c$ be real numbers with $\nu_f(t) \le c\,\alpha^t$ for every $t \ge 0$. Then the sequence $\beta_f(t)^{1/t}$ is eventually bounded above and
--   $$\limsup_{t\to\infty} \beta_f(t)^{1/t} \le g(\alpha), \qquad g(\alpha) = \begin{cases} 2\sqrt{2k-1} & \alpha \le \sqrt{2k-1}, \\ \frac{2k-1}{\alpha} + \alpha & \text{otherwise.} \end{cases}$$
--   The boundedness conjunct makes the real-valued limit superior the usual one.
--
--   Puder, p. 18: “**Theorem 4.4.** [Extended Cogrwoth Formula [Pud15]] *Let $d \ge 3$, $f : V(T_d) \to \mathbb R$, $\beta_f(t)$ and $\nu_f(t)$ as above. If $\nu_f(t) \le c \cdot \alpha^t$ for every $t$ (and some $c > 0$) then $$\limsup_{t\to\infty} \beta_f(t)^{1/t} \le g(\alpha).$$*” On pp. 17–18, $g : [1, d-1] \to [2\sqrt{d-1}, d]$ is “$g(\alpha) = 2\sqrt{d-1}$ for $\alpha \le \sqrt{d-1}$, $\frac{d-1}{\alpha} + \alpha$ for $\alpha \ge \sqrt{d-1}$” (4.4), $\beta_f(t) = \sum_{p} f(\mathrm{end}(p))$ over “all (possibly backtracking) walks of length $t$ in $T_d$ emanating from ⊗”, and $\nu_f(t)$ is “the same sum over the smaller set of non-backtracking walks”. (“Cogrwoth” is the print's spelling.)
--
--   *Formalization note.* This is the case $d = 2k$, $T_d$ the Cayley graph of $\mathbf F_k$, which is the form Puder applies in the proof of Corollary 4.5 (“Consider the the Cayley graph of $\mathbf F_k$ which is a $2k$-regular tree”); odd $d$ is not stated. Two hypotheses are made explicit. The function $f$ is nonnegative, which Puder's application has ($f_m(w) = \mathbb 1_{\pi(w)=m}|\mathrm{Crit}(w)|$); for a sign-changing $f$ the sum $\beta_f(t)$ can be negative, where $\beta_f(t)^{1/t}$ is not defined in the print. And $\alpha \ge 0$: Puder's $g$ is defined on $[1, d-1]$, and the statement here allows any $\alpha \ge 0$. The constant $c$ is any real number.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, pp. 17–18), Theorem 4.4, which cites D. Puder, *Notes on the cogrowth formula: the regular, biregular and irregular cases*, preprint (cited as [Pud15]; no DOI).
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), pp. 17–18, Theorem 4.4 (extended cogrowth formula), which cites Puder, D., Notes on the cogrowth formula: the regular, biregular and irregular cases, preprint ([Pud15])

import Mathlib
import Definitions.Def_StrongConv

open Filter

namespace Puder

theorem limsup_sum_rpow_le_cogrowth (k : ℕ) (hk : 2 ≤ k) (f : FreeGroup (Fin k) → ℝ)
    (hf : ∀ g, 0 ≤ f g) (α c : ℝ) (hα : 0 ≤ α)
    (hν : ∀ t : ℕ, ∑ i : Fin t → Fin k ⊕ Fin k with
        (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap),
        f (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≤ c * α ^ t) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) ^
          (1 / (t : ℝ))) atTop ≤
        if α ≤ Real.sqrt (2 * k - 1) then 2 * Real.sqrt (2 * k - 1) else (2 * k - 1) / α + α := by
  sorry

end Puder
