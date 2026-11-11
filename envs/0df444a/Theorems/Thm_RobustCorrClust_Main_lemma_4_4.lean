-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_4_4
-- name    : RobustCorrClust.Main.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:40:40.982386+00:00
-- url     : https://prove2.me/theorems/27db502e-333a-427a-854a-92af6afb2f04
-- title:
--   Lemma 4.4 — 0 ≤ Ψ_G ≤ Ψ_H̃ on Eₙ, and Ψ_H̃(O^{C*}) ≤ (1 + O(ε))·OPT
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $G$ be a complete signed graph on $n$ vertices, $0<\varepsilon<1/2$, $H$ a $(1\pm\varepsilon)$-spectral sparsifier of the positive graph $G^+$ (Definition 2) and $\tilde H$ its rescaling (weights $w_H/(1-\varepsilon)$). Then
--
--   1. $0\le\Psi_G(Y)\le\Psi_{\tilde H}(Y)$ for every $Y\in E_n$ (real symmetric positive semidefinite with unit diagonal);
--   2. for every optimal clustering $\mathcal C^*$ of $G$, with cluster matrix $O^{\mathcal C^*}$,
--   $$\Psi_{\tilde H}(O^{\mathcal C^*})\le(1+c\,\varepsilon)\,\mathrm{OPT}(G).$$
--
--   The sparsified objective is thus an upper bound on the true square loss over the elliptope that loses only a $1+O(\varepsilon)$ factor at the optimal clustering.
--
--   Differences from the source:
--   - encoding: $(1+O(\varepsilon))$ → $(1+c\varepsilon)$ with one constant $c>0$ fixed before $n,G,H,\varepsilon$; reason: the meaning of the $O(\cdot)$ (the proof gives $2\frac{1+\varepsilon}{1-\varepsilon}-1\le1+8\varepsilon$).
--   - reading: the range of $\varepsilon$ → $0<\varepsilon<1/2$; reason: the proof states the bound "for any $\varepsilon<1/2$", and $\varepsilon$ is a positive accuracy.
--   - encoding: "the optimal clustering $C^*$" → every optimal clustering; reason: the statement is about any minimizer of the cost.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 19, Lemma 4.4

import Mathlib
import Definitions.Def_UniversalSubmod_CorrMatrix
import Definitions.Def_RobustCorrClust_Main_Sparsifier

namespace RobustCorrClust.Main

/-- Lemma 4.4 (p. 19): for a `(1 ± ε)`-spectral sparsifier `H` of the positive graph `G⁺`
(`0 < ε < 1/2`) and its rescaling `H̃`, (i) `0 ≤ Ψ_G(Y) ≤ Ψ_H̃(Y)` for every `Y ∈ Eₙ`, and
(ii) `Ψ_H̃(O^{C*}) ≤ (1 + O(ε)) OPT` for every optimal clustering `C*`, with one absolute
constant `c` in the `O(ε)`. -/
theorem lemma_4_4 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (H : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ),
        0 < ε → ε < 1 / 2 → IsSpectralSparsifier ε (adjMat G) H →
        (∀ Y : Matrix (Fin n) (Fin n) ℝ, UniversalSubmod.CorrMatrix Y →
            0 ≤ PsiG G Y ∧ PsiG G Y ≤ PsiTilde G (rescale ε H) Y) ∧
        (∀ Cstar : Setoid (Fin n), IsOptimal G Cstar →
            PsiTilde G (rescale ε H) (clusterMat Cstar) ≤ (1 + c * ε) * (OPT G : ℝ)) := by sorry

end RobustCorrClust.Main
