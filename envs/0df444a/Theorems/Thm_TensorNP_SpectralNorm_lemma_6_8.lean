-- Prove2me | Theorems.Thm_TensorNP_SpectralNorm_lemma_6_8
-- name    : TensorNP.SpectralNorm.lemma_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:54.416046+00:00
-- url     : https://prove2.me/theorems/3f4a7deb-473e-43d8-927a-67923fb2bc9f
-- title:
--   Lemma 6.8 — M_l = N_l for every graph
-- statement:
--   Let $G$ be a simple graph on $v\ge1$ vertices with edges $\{i_k,j_k\}$, $k=1,\dots,e$, enumerated in any order, and let $l$ be a positive integer. With $M_l=\max_{\mathbf x\in\Delta_v}\mathbf x^\top Q_l\mathbf x$ and
--   $$
--   N_l=\max_{\|\mathbf u\|_2=1}\Big\{\sum_{i=1}^l\Big(\mathbf u^\top\tfrac1lI\mathbf u\Big)^2+2\sum_{k=1}^e(\mathbf u^\top E_k\mathbf u)^2\Big\},
--   $$
--   where $E_k=\frac12E_{i_kj_k}+\frac12E_{j_ki_k}$, we have
--   $$
--   M_l=N_l .
--   $$
--
--   The lemma rewrites the simplex program $M_l$ as an optimization over the unit sphere, in the form that the Cauchy–Schwarz step of Lemma 6.11 produces.
--
--   **Formalization Note** Both maxima are the `sSup`-based definitions `Mval` and `Nval`; the statement holds for every enumeration `ε : Fin e ≃ G.edgeSet`. The hypotheses $v\ge1$ and $l\ge1$ are the section's standing assumptions.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:23, Lemma 6.8

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor
import Definitions.Def_TensorNP_SpectralNorm_CliqueTensor

namespace TensorNP.SpectralNorm

/-- **Lemma 6.8.** For every simple graph `G` on `v ≥ 1` vertices, every enumeration `ε` of its
edges and every positive integer `l`, `M_l = N_l`. -/
theorem lemma_6_8 {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) :
    Mval G l = Nval G ε l := by sorry

end TensorNP.SpectralNorm
