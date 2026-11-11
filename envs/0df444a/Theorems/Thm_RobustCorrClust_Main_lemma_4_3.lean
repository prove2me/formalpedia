-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_4_3
-- name    : RobustCorrClust.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:40:40.887297+00:00
-- url     : https://prove2.me/theorems/8e3390c7-5750-4c21-8da2-a9eab9fd1bac
-- title:
--   Lemma 4.3 — Ψ_G(Y) = ⟨L_{G⁺}, Y⟩ + ½‖Y‖²_F − n/2 − m for symmetric Y with unit diagonal
-- statement:
--   Let $G$ be a complete signed graph on $n$ vertices with $m$ positive pairs, $A$ its adjacency matrix and $L_{G^+}$ the Laplacian of its positive graph. For every real symmetric $n\times n$ matrix $Y$ with $Y_{uu}=1$ for all $u$ (in particular for every $Y\in E_n$),
--   $$\Psi_G(Y)=\sum_{u<v}(Y_{uv}-A_{uv})^2=\langle L_{G^+},Y\rangle+\tfrac12\|Y\|_F^2-\tfrac n2-m .$$
--   The identity rewrites the square loss of the SDP relaxation as a linear function of $Y$ plus half the squared Frobenius norm; it is what allows the input graph to be replaced by a spectral sparsifier.
--
--   Differences from the source:
--   - reading: "For every $Y\in E_n$ … Furthermore … we only need diag(Y) = 1, we do not need the positive semi-definite condition" → one statement for every symmetric $Y$ with unit diagonal; reason: the paper's matrices live in $S^n$, the second sentence drops only positive semidefiniteness, and the $E_n$ case is contained.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 18, Lemma 4.3

import Mathlib
import Definitions.Def_RobustCorrClust_Main_Sparsifier

namespace RobustCorrClust.Main

/-- Lemma 4.3 (p. 18), in its "Furthermore" form: for every symmetric `Y` with unit diagonal
(in particular every `Y ∈ Eₙ`), `Ψ_G(Y) = ⟨L_{G⁺}, Y⟩ + ½‖Y‖²_F − n/2 − m`. -/
theorem lemma_4_3 {n : ℕ} (G : SimpleGraph (Fin n)) (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : Y.IsSymm) (hdiag : ∀ u, Y u u = 1) :
    PsiG G Y = frobInner (lap (adjMat G)) Y + frobSq Y / 2 - (n : ℝ) / 2 - (numPos G : ℝ) := by sorry

end RobustCorrClust.Main
