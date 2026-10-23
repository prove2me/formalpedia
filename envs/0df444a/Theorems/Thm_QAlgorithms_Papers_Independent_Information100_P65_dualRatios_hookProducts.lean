-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P65_dualRatios_hookProducts
-- name    : QAlgorithms.Papers.Independent.Information100.P65.dualRatios_hookProducts
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:50:26.392052+00:00
-- url     : https://prove2.me/theorems/fa2377a7-f847-4792-a69e-c148454f0234
-- title:
--   Lemma 3.18: Dual dimension ratios become hook products
-- statement:
--   Let $\lambda^+$ be a Young diagram with at most $d\ge1$ rows, let $(j,m)$ be a removable box, and set $\lambda=\lambda^+-e_j$. Fix an integer $R\ge\lambda_1^+$ and complement diagrams in the $d\times R$ rectangle, with a half-turn: $\mu^c=(R-\mu_d,\ldots,R-\mu_1)$. The dual pair has lower diagram $(\lambda^+)^c$, upper diagram $\lambda^c$, and addition row $j'=d+1-j$. Write $\kappa'_n=D_n(\lambda^c)/D_n((\lambda^+)^c)$. Then, for $1\le k\le j$,
--
--   $$\frac{\kappa'_{j'+k-1}}{\kappa'_d}=\prod_{i=1}^{j-k}\left(1-\frac1{h_{(i,m)}(\lambda^+)}\right).$$
--
--   The hooks belong to the original upper diagram, and the empty product for $k=j$ is one. This identity converts the adding-channel dimension ratios of the dual pair to the removing-channel hook products.
--
--   **Formalization Note** Complemented rows are computed from the original diagram. Dimension ratios use Weyl's product formula. Both row and column indices of hook cells are shifted down by one in Lean.
-- source:
--   Minimal output entropy for the channels that add or remove a box of a Young diagram, and a Pauli principle for every permutation symmetry, arXiv:2609.33498v1, PDF p. 19, Lemma 3.18: Dual dimension ratios become hook products

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P65

attribute [local instance] Classical.propDecidable

/-- Lemma 3.18, dual dimension ratios are original hook products
(arxiv-2609.33498v1, PDF p.19). Complemented diagrams are computed from the
original pair. The dual lower diagram is upper^c and its addition row is
zero-based d-1-j. Hook cells use zero-based column upper.rowLen j-1. -/
theorem dualRatios_hookProducts {d j R k : ℕ} (lower upper : YoungDiagram)
    (hpair : IsBoxPair d lower upper j) (hR : upper.rowLen 0 ≤ R)
    (hk : 1 ≤ k) (hkj : k ≤ j + 1) :
    dimensionRatio (complementRows upper R d) (d - 1 - j) (d - 1 - j + k) /
      dimensionRatio (complementRows upper R d) (d - 1 - j) d =
      ∏ a ∈ Finset.range (j + 1 - k),
        (1 - 1 / (hookLength upper a (upper.rowLen j - 1) : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P65

end
