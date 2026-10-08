-- Prove2me | Theorems.Thm_TensorNP_SpectralNorm_lemma_6_11
-- name    : TensorNP.SpectralNorm.lemma_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:56.381268+00:00
-- url     : https://prove2.me/theorems/6d7be084-ad36-450b-82b9-776d10075ea0
-- title:
--   Lemma 6.11 — T_l = M_l^{1/2}; T_l = 1 iff l = ω, T_l > 1 iff l < ω, T_l < 1 iff l > ω
-- statement:
--   Let $G$ be a simple graph on $v\ge1$ vertices with clique number $\omega$ and edges enumerated as $\{i_k,j_k\}$, $k=1,\dots,e$, and let $l$ be a positive integer. Let
--   $$
--   T_l=\max_{\|\mathbf u\|_2=\|\mathbf v\|_2=\|\mathbf w\|_2=1}\Big\{\sum_{i=1}^l\Big(\mathbf u^\top\tfrac1lI\mathbf v\Big)w_i+\sum_{k=1}^e(\mathbf u^\top E_k\mathbf v)w_{l+k}+\sum_{k=1}^e(\mathbf u^\top E_k\mathbf v)w_{e+l+k}\Big\}, \tag{26}
--   $$
--   with $\mathbf u,\mathbf v\in\mathbb R^v$ and $\mathbf w\in\mathbb R^{l+2e}$. Then
--   $$
--   T_l=M_l^{1/2},
--   $$
--   and therefore $T_l=1$ iff $l=\omega$, $T_l>1$ iff $l<\omega$, and $T_l<1$ iff $l>\omega$.
--
--   This identifies the maximum of the multilinear form (26), the form of the tensor $\mathcal A_l$, with the square root of the Motzkin–Straus quantity $M_l$, so that its comparison with $1$ detects the clique number.
--
--   **Formalization Note** $T_l$ and $M_l$ are the `sSup`-based definitions `Tval` and `Mval`; the statement holds for every edge enumeration. The paper's statement of Lemma 6.11 prints $w_{m+l+k}$ in the third sum; there is no $m$ in this section and the proof (p. 0:24) uses $w_{e+l+k}$, which is formalized here (0-based: coordinates $l+e,\dots,l+2e-1$ of $\mathbf w$).
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), pp. 0:23–0:24, Lemma 6.11, (26), and its proof

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor
import Definitions.Def_TensorNP_SpectralNorm_CliqueTensor

namespace TensorNP.SpectralNorm

/-- **Lemma 6.11.** For a simple graph `G` on `v ≥ 1` vertices with clique number `ω`, any
enumeration `ε` of its `e` edges and any positive integer `l`, the maximum `T_l` of the form (26)
over `‖u‖₂ = ‖v‖₂ = ‖w‖₂ = 1` equals `M_l^{1/2}`; thus `T_l = 1` iff `l = ω`, `T_l > 1` iff
`l < ω`, and `T_l < 1` iff `l > ω`. -/
theorem lemma_6_11 {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) :
    Tval G ε l = Real.sqrt (Mval G l) ∧
      (Tval G ε l = 1 ↔ l = G.cliqueNum) ∧
      (1 < Tval G ε l ↔ l < G.cliqueNum) ∧
      (Tval G ε l < 1 ↔ G.cliqueNum < l) := by sorry

end TensorNP.SpectralNorm
