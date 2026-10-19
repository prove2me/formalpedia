-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_sequential_converse
-- name    : QAlgorithms.Papers.Independent.Information100.P62.sequential_converse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:39:24.00719+00:00
-- url     : https://prove2.me/theorems/e892af0d-c078-4185-af67-d3392e5874aa
-- title:
--   Remark 3.9: sequential and two-block converses
-- statement:
--   For every transmittable shape $(d_1,\ldots,d_m)$ one can select Kraus indices $i_k$ so that, with $V_k=\operatorname{span}_{l<k}\operatorname{im}E_{i_l}$,
--   $$d_k\le\operatorname{rank}E_{i_k}-[\operatorname{rank}(\Pi_{V_k}E_{i_k})-\dim V_k+\sum_{l<k}d_l]_+\le\operatorname{rank}E_{i_k}.$$
--   For two blocks $d\ge e>0$, selected labels $i,j$ satisfy $d\le\operatorname{rank}E_i$ and $e\le\operatorname{rank}E_j-[\operatorname{rank}(E_i^*E_j)-\operatorname{rank}E_i+d]_+$. If $i=j$, their ranks fit the sum $d+e$; if $\operatorname{rank}E_i=d$, then $e+\operatorname{rank}(E_i^*E_j)\le\operatorname{rank}E_j$. The overlap rank equals $\operatorname{rank}(\Pi_{\operatorname{im}E_i}E_j)$. These are conditional consequences for existentially selected labels.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 26, Remark 3.9: sequential and two-block converses

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.26, Remark 3.9: sequential and two-block converses. -/
theorem sequential_converse [Nonempty I] [Nonempty O]
    {r : ℕ} (E : Fin r → Matrix O I ℂ) (hE : IsKrausFamily E) :
    (∀ A : Shape, Transmits (krausApply E) A → ∃ f : Block A → Fin r,
      ∀ k : Block A,
        (blockSize A k : ℤ) + max 0
          (((projection (selectedSpan E f (univ.filter (fun j => j < k))) * E (f k)).rank : ℤ) -
            Module.finrank ℂ (selectedSpan E f (univ.filter (fun j => j < k))) +
            ∑ j ∈ univ.filter (fun j => j < k), (blockSize A j : ℤ)) ≤ (E (f k)).rank) ∧
    (∀ d e : ℕ, 0 < e → e ≤ d → Transmits (krausApply E) (quantum d + quantum e) →
      ∃ i j : Fin r, d ≤ (E i).rank ∧
        (e : ℤ) + max 0 (((E i)ᴴ * E j).rank - ((E i).rank : ℤ) + d) ≤ (E j).rank ∧
        (i = j → d + e ≤ (E i).rank) ∧
        (((E i).rank = d) → e + ((E i)ᴴ * E j).rank ≤ (E j).rank) ∧
        ((E i)ᴴ * E j).rank = (projection (imageSpace (E i)) * E j).rank) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
