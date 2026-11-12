-- Prove2me | Theorems.Thm_Puder_tendsto_card_reduced_isPrimitiveIn_top_rpow_sqrt_three
-- name    : Puder.tendsto_card_reduced_isPrimitiveIn_top_rpow_sqrt_three
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T14:25:35.509206+00:00
-- url     : https://prove2.me/theorems/a99893ed-bc15-4f55-9de3-8904a3279947
-- title:
--   Rivin (Puder, p. 36) — the number p_2(t) of primitive words of length t in F_2 satisfies p_2(t)^{1/t} → √3
-- statement:
--   Let $p_2(t)$ be the number of primitive elements of $\mathbf F_2$ (elements of some basis of $\mathbf F_2$, `Puder.IsPrimitiveIn ⊤`) of reduced length $t$ with respect to $g_1, g_2$. In the Lean, it is the number of letter sequences of length $t$ in $g_1^{\pm 1}, g_2^{\pm 1}$ whose reduction (`StrongConv.wordFree`) has length $t$ (`FreeGroup.toWord`) and is primitive. Then
--   $$\lim_{t \to \infty} p_2(t)^{1/t} = \sqrt 3.$$
--
--   Puder, p. 36, after Theorem 8.1 (which concerns $p_k(t)$, “the number of primitive words of length $t$ in $\mathbf F_k$”, for $k \ge 3$): “For $\mathbf F_2$ it is known that this exponential growth rate equals $\sqrt 3$ ([Riv04]).”
--
--   *Formalization note.* “This exponential growth rate” is read as the limit in Theorem 8.1, $\lim_{t\to\infty} p_2(t)^{1/t}$.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 36), citing I. Rivin, *A remark on “Counting primitive elements in free groups” (by J. Burillo and E. Ventura)*, Geom. Dedicata 107 (2004) 99–100, https://doi.org/10.1023/B:GEOM.0000049102.82732.1f.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 36, the sentence after Theorem 8.1 (F_2), which cites I. Rivin, A remark on "Counting primitive elements in free groups", Geom. Dedicata 107 (2004) 99–100, https://doi.org/10.1023/B:GEOM.0000049102.82732.1f

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

open Filter Topology

namespace Puder

open Classical in
theorem tendsto_card_reduced_isPrimitiveIn_top_rpow_sqrt_three :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin 2 ⊕ Fin 2 =>
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              IsPrimitiveIn ⊤ (StrongConv.wordFree (List.ofFn fun j => some (i j)))).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (Real.sqrt 3)) := by
  sorry

end Puder
