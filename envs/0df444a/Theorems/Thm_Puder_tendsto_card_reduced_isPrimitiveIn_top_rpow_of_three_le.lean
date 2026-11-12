-- Prove2me | Theorems.Thm_Puder_tendsto_card_reduced_isPrimitiveIn_top_rpow_of_three_le
-- name    : Puder.tendsto_card_reduced_isPrimitiveIn_top_rpow_of_three_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T14:25:39.835349+00:00
-- url     : https://prove2.me/theorems/cd66b691-a866-4b5c-a795-5e635b083bb6
-- title:
--   Puder–Wu (Puder, Theorem 8.1) — the number p_k(t) of primitive words of length t in F_k satisfies p_k(t)^{1/t} → 2k − 3 for k ≥ 3
-- statement:
--   Let $k \ge 3$ and let $p_k(t)$ be the number of primitive elements of $\mathbf F_k$ (elements of some basis of $\mathbf F_k$, `Puder.IsPrimitiveIn ⊤`) of reduced length $t$ with respect to $g_1, \dots, g_k$. In the Lean, it is the number of letter sequences of length $t$ in $g_i$ and $g_i^{-1}$ whose reduction (`StrongConv.wordFree`) has length $t$ (`FreeGroup.toWord`) and is primitive; these are the reduced words, one for each such element. Then
--   $$\lim_{t \to \infty} p_k(t)^{1/t} = 2k - 3.$$
--
--   Puder, p. 36: “**Theorem 8.1.** [PW14] *For every $k \ge 3$, let $p_k(t)$ denote the number of primitive words of length $t$ in $\mathbf F_k$. Then, $$\lim_{t\to\infty} p_k(t)^{1/t} = 2k - 3.$$*”
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 36), Theorem 8.1, which cites D. Puder and C. Wu, *Growth of primitive elements in free groups*, J. Lond. Math. Soc. (2) 90 (2014) 89–104, https://doi.org/10.1112/jlms/jdu009.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 36, Theorem 8.1, which cites Puder, D. and Wu, C., Growth of primitive elements in free groups, J. Lond. Math. Soc. (2) 90 (2014) 89–104, https://doi.org/10.1112/jlms/jdu009

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

open Filter Topology

namespace Puder

open Classical in
theorem tendsto_card_reduced_isPrimitiveIn_top_rpow_of_three_le (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              IsPrimitiveIn ⊤ (StrongConv.wordFree (List.ofFn fun j => some (i j)))).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (2 * k - 3)) := by
  sorry

end Puder
