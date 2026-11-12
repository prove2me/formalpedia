-- Prove2me | Theorems.Thm_Puder_limsup_sum_ncard_isAlgExt_reduced_rpow_le
-- name    : Puder.limsup_sum_ncard_isAlgExt_reduced_rpow_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T14:00:22.188192+00:00
-- url     : https://prove2.me/theorems/6b20e2a0-803e-4049-84ca-a133478d9409
-- title:
--   Puder, proof of Proposition 4.3 — growth of the count of proper algebraic extensions of rank m of ⟨w⟩, over reduced words w of length t
-- statement:
--   Let $k \ge 2$ and $1 \le m \le k$. For $t \ge 0$ let
--   $$c_t = \sum_{\substack{w \in \mathbf F_k \\ |w| = t}} \big|\{J \le \mathbf F_k : \mathrm{rk}(J) = m,\ \langle w \rangle \lneq_{alg} J\}\big|,$$
--   the sum over the elements $w$ of $\mathbf F_k$ of reduced length $t$ of the number of subgroups $J$ that are free of rank $m$ (`Puder.HasRank J m`) and algebraic extensions of $\langle w \rangle$ (`Puder.IsAlgExt (Subgroup.zpowers w) J`) different from $\langle w \rangle$. As in Proposition 4.3, the sum runs over the letter sequences of length $t$ in $g_i^{\pm 1}$ whose reduction (`StrongConv.wordFree`) has length $t$, one for each such $w$. Then $c_t^{1/t}$ is eventually bounded above and
--   $$\limsup_{t \to \infty} c_t^{1/t} \le \begin{cases} \sqrt{2k-1} & 2m - 1 \le \sqrt{2k-1}, \\ 2m - 1 & \text{otherwise.} \end{cases}$$
--   The count is `Set.ncard`, which is $0$ for an infinite set; the set is finite by Takahasi's theorem (`Puder.setOf_isAlgExt_finite_of_fg`).
--
--   Puder, p. 16, proof of Proposition 4.3: “Note that $$\sum_{\substack{w \in \mathbf F_k: \\ |w| = t\ \&\ \pi(w) = m}} |\mathrm{Crit}(w)| = \sum_{J \le \mathbf F_k: \mathrm{rk}(J) = m} |\{w \in \mathbf F_k \mid |w| = t,\ J \in \mathrm{Crit}(w)\}| \le \sum_{J \le \mathbf F_k: \mathrm{rk}(J) = m} |\{w \in \mathbf F_k \mid |w| = t,\ \langle w \rangle \lneq_{alg} J\}| \quad (4.1)$$ $$\le \sum_{J \le \mathbf F_k: \mathrm{rk}(J) = m} \Big|\Big\{w \in J \;\Big|\; \begin{matrix} |w| = t,\ w \text{ traces each edge} \\ \text{of } \Gamma_X(J) \text{ at least twice} \end{matrix}\Big\}\Big|,$$ where the first inequality stems from Claim 3.1 and the second from Lemma 4.1.” Then, p. 17, after bounding the last line: “When $2m - 1 \le \sqrt{2k-1}$, the r.h.s. of (4.2) is largest when $\delta = \frac12$, so we get overall $$\sum_{J \le \mathbf F_k: rk(J) = m} \nu_t(J) \le c \cdot t^{10m-1} \cdot \big[\sqrt{2k-1}\big]^t. \quad (4.3)$$ For $2m - 1 \ge \sqrt{2k-1}$, the r.h.s. of (4.2) is largest when $\delta = 0$, so we get overall $$\sum_{J \le \mathbf F_k: rk(J) = m} \nu_t(J) \le c \cdot t^{10m-1} \cdot [2m-1]^t.$$”
--
--   *Formalization note.* The statement is the bound Puder's argument gives for the middle line of (4.1), summed over $w$ rather than over $J$ (the two orders give the same total). Puder bounds it through the last line, using Lemma 4.1 and the count of core graphs on pp. 16–17.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, pp. 16–17), proof of Proposition 4.3.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), pp. 16–17, proof of Proposition 4.3, the middle line of (4.1) and its bound (4.2)–(4.3)

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg

open Filter

namespace Puder

theorem limsup_sum_ncard_isAlgExt_reduced_rpow_le (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
              IsAlgExt (Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j)))) J ∧
              Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≠ J}.ncard : ℝ)) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
              IsAlgExt (Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j)))) J ∧
              Subgroup.zpowers (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≠ J}.ncard : ℝ)) ^
          (1 / (t : ℝ))) atTop ≤
        if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1) then Real.sqrt (2 * k - 1) else 2 * m - 1 := by
  sorry

end Puder
