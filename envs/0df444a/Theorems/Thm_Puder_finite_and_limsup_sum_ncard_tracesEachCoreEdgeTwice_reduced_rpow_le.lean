-- Prove2me | Theorems.Thm_Puder_finite_and_limsup_sum_ncard_tracesEachCoreEdgeTwice_reduced_rpow_le
-- name    : Puder.finite_and_limsup_sum_ncard_tracesEachCoreEdgeTwice_reduced_rpow_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T14:37:44.396366+00:00
-- url     : https://prove2.me/theorems/8d5a13c9-cf9a-4cd2-971a-a588ffa017ca
-- title:
--   Puder, proof of Proposition 4.3 — growth of the count of rank-m subgroups J ∋ w whose core graph w traces twice, over reduced words w of length t
-- statement:
--   Let $k \ge 2$ and $1 \le m \le k$. For each $w \in \mathbf F_k$ the set
--   $$T_w = \{J \le \mathbf F_k : \mathrm{rk}(J) = m,\ w \in J,\ w \text{ traces each edge of } \Gamma_X(J) \text{ at least twice}\}$$
--   is finite (`Puder.HasRank`, `Puder.TracesEachCoreEdgeTwice`). Let $s_t = \sum_{|w| = t} |T_w|$, the sum over the elements $w$ of reduced length $t$. As in Proposition 4.3, it runs over the letter sequences of length $t$ in $g_i^{\pm1}$ whose reduction (`StrongConv.wordFree`) has length $t$. Then $s_t^{1/t}$ is eventually bounded above and
--   $$\limsup_{t \to \infty} s_t^{1/t} \le \begin{cases} \sqrt{2k-1} & 2m - 1 \le \sqrt{2k-1}, \\ 2m - 1 & \text{otherwise.} \end{cases}$$
--
--   Puder, p. 16, proof of Proposition 4.3: the last line of (4.1) is “$$\sum_{J \le \mathbf F_k: \mathrm{rk}(J) = m} \Big|\Big\{w \in J \;\Big|\; \begin{matrix} |w| = t,\ w \text{ traces each edge} \\ \text{of } \Gamma_X(J) \text{ at least twice} \end{matrix}\Big\}\Big|$$” and “For each $J \le \mathbf F_k$ let $\nu_t(J)$ denote the corresponding summand”. Then, p. 17: “When $2m - 1 \le \sqrt{2k-1}$, the r.h.s. of (4.2) is largest when $\delta = \frac12$, so we get overall $$\sum_{J \le \mathbf F_k: rk(J) = m} \nu_t(J) \le c \cdot t^{10m-1} \cdot \big[\sqrt{2k-1}\big]^t. \quad (4.3)$$ For $2m - 1 \ge \sqrt{2k-1}$, the r.h.s. of (4.2) is largest when $\delta = 0$, so we get overall $$\sum_{J \le \mathbf F_k: rk(J) = m} \nu_t(J) \le c \cdot t^{10m-1} \cdot [2m-1]^t.$$”
--
--   *Formalization note.* The sum is taken over $w$ rather than over $J$; the two orders give the same total $\sum_J \nu_t(J)$. Only the exponential rate of (4.3) is stated, not the polynomial factor $c\,t^{10m-1}$. The finiteness of each $T_w$ is implicit in Puder's sum and is stated as its own conjunct.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, pp. 16–17), proof of Proposition 4.3.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), pp. 16–17, proof of Proposition 4.3, the last line of (4.1) and its bound (4.2)–(4.3)

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderCore

open Filter

namespace Puder

theorem finite_and_limsup_sum_ncard_tracesEachCoreEdgeTwice_reduced_rpow_le (k m : ℕ) (hk : 2 ≤ k)
    (hm1 : 1 ≤ m) (hm : m ≤ k) :
    (∀ w : FreeGroup (Fin k),
        {J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ w ∈ J ∧ TracesEachCoreEdgeTwice J w}.Finite) ∧
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
              TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard : ℝ)) ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
              TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard : ℝ)) ^ (1 / (t : ℝ))) atTop ≤
        if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1) then Real.sqrt (2 * k - 1) else 2 * m - 1 := by
  sorry

end Puder
