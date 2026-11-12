-- Prove2me | Theorems.Thm_Puder_tendsto_card_reduced_primitivityRank_eq_rpow_of_sqrt_lt
-- name    : Puder.tendsto_card_reduced_primitivityRank_eq_rpow_of_sqrt_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T14:25:28.611931+00:00
-- url     : https://prove2.me/theorems/e3130e77-e42d-47f8-a797-9ea36f93d685
-- title:
--   Puder, Theorem 8.2 for 2m − 1 > √(2k−1) — the number c_{k,m}(t) of words of length t with π = m satisfies c_{k,m}(t)^{1/t} → 2m − 1
-- statement:
--   Let $k \ge 2$ and $m \le k$ with $2m - 1 > \sqrt{2k-1}$ (so $m \ge 2$). Let $c_{k,m}(t)$ be the number of elements $w \in \mathbf F_k$ of reduced length $t$ (with respect to $g_1, \dots, g_k$) whose primitivity rank is $m$ (`Puder.primitivityRank`). In the Lean, it is the number of letter sequences of length $t$ in $g_i$ and $g_i^{-1}$ whose reduction (`StrongConv.wordFree`) has length $t$ (`FreeGroup.toWord`) and primitivity rank $m$; these are the reduced words, one for each such element. Then
--   $$\lim_{t \to \infty} c_{k,m}(t)^{1/t} = 2m - 1.$$
--
--   Puder, p. 37: “**Theorem 8.2.** *Let $k \ge 2$ and $m \in \{1, 2, \dots, k\}$. Let $$c_{k,m}(t) = |\{w \in \mathbf F_k \mid |w| = t,\ \pi(w) = m\}|.$$ Then, $$\limsup_{t\to\infty} c_{k,m}(t)^{1/t} = \begin{cases} \sqrt{2k-1} & 2m-1 \le \sqrt{2k-1} \\ 2m-1 & 2m-1 \ge \sqrt{2k-1} \end{cases}. \quad (8.1)$$* In fact, as the proof shows, for $m \ge 2$, we can replace the lim sup with regular lim, …” and, in the proof: “Consider first the case $2m - 1 > \sqrt{2k-1}$. … In particular, we proved that for such values of $m$, $$\limsup_{t\to\infty} c_{k,m}(t)^{1/t} = \lim_{t\to\infty} c_{k,m}(t)^{1/t} = 2m - 1.$$”
--
--   *Formalization note.* Only the case $2m - 1 > \sqrt{2k-1}$ is stated, in the form the last quoted sentence gives (a limit). It is the case Puder's proof of Theorem 8.5 uses for $2m - 1 > \sqrt{2k-1}$ (p. 38).
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 37), Theorem 8.2.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 37, Theorem 8.2, the case 2m − 1 > √(2k − 1)

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

open Filter Topology

namespace Puder

theorem tendsto_card_reduced_primitivityRank_eq_rpow_of_sqrt_lt (k m : ℕ) (hk : 2 ≤ k) (hm : m ≤ k)
    (hlt : Real.sqrt (2 * k - 1) < 2 * m - 1) :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (2 * m - 1)) := by
  sorry

end Puder
