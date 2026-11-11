-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_6_8
-- name    : RobustCorrClust.Main.lemma_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:40:41.453873+00:00
-- url     : https://prove2.me/theorems/65b98bf9-bbce-4a32-b71f-dfbfc271e439
-- title:
--   Lemma 6.8 — joint squared-error bound Σ_{u<v}[(Ŷ − A)² + (Ŷ − O^{C*})²] ≤ (1 + O(ε))·OPT(G)
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $G$ be a complete signed graph on $n$ vertices with adjacency matrix $A$, $\varepsilon\in(0,10^{-3}]$, $H$ a $(1\pm\varepsilon)$-spectral sparsifier of $G^+$ and $\tilde H$ its rescaling. Let $Y\in E_n$ with
--   $$\Psi_{\tilde H}(Y)\le\min_{Z\in E_n}\Psi_{\tilde H}(Z)+\varepsilon^2,$$
--   let $\hat Y$ be a real matrix with $|\hat Y_{uv}-Y_{uv}|\le\varepsilon/n$ for all $u\ne v$ (the column-query accuracy $\gamma=\varepsilon/n$), and let $\mathcal C^*$ be an optimal clustering of $G$. If $\mathrm{OPT}(G)\ge1$, then
--   $$\sum_{u<v}\Big[(\hat Y_{uv}-A_{uv})^2+(\hat Y_{uv}-O^{\mathcal C^*}_{uv})^2\Big]\le(1+c\,\varepsilon)\,\mathrm{OPT}(G).$$
--   Together with Lemma 6.7 this bounds the expected cost of the threshold rounding.
--
--   Differences from the source:
--   - encoding: $(1+O(\varepsilon))$ → $(1+c\varepsilon)$ with one constant $c>0$ fixed before $n,G,H,Y,\hat Y,\varepsilon$; reason: the meaning of the $O(\cdot)$.
--   - generalization: $\hat Y$ the (symmetric) output of Algorithm 2 with $\gamma=\varepsilon/n$, $Y$ the matrix of Part B, $H$ the sparsifier of Proposition 3.2 → any matrix $\hat Y$ within $\varepsilon/n$ of $Y$ off the diagonal, any $Y\in E_n$ with the §6.1 near-optimality, any $(1\pm\varepsilon)$-spectral sparsifier $H$; reason: the lemma uses only these properties (Theorem 3 (ii), §6.1, Definition 2), which the paper's objects have.
--   - encoding: $\le\min_{Z\in E_n}\Psi_{\tilde H}(Z)+\varepsilon^2$ → $\le\Psi_{\tilde H}(Z)+\varepsilon^2$ for every $Z\in E_n$; reason: equivalent.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 52, Lemma 6.8; setting p. 44, §6.1

import Mathlib
import Definitions.Def_UniversalSubmod_CorrMatrix
import Definitions.Def_RobustCorrClust_Main_Sparsifier

namespace RobustCorrClust.Main

/-- Lemma 6.8 (p. 52) in the setting of §6.1 (p. 44): `ε ∈ (0, 10⁻³]`, `H` a `(1 ± ε)`-spectral
sparsifier of `G⁺` with rescaling `H̃`, `Y ∈ Eₙ` with `Ψ_H̃(Y) ≤ min_{Z ∈ Eₙ} Ψ_H̃(Z) + ε²`,
column-query values `Ŷ_uv` within `γ = ε/n` of `Y_uv` for `u ≠ v`, and `C*` an optimal
clustering of `G`. If `OPT(G) ≥ 1`, then
`∑_{u<v} [(Ŷ_uv − A_uv)² + (Ŷ_uv − O^{C*}_uv)²] ≤ (1 + O(ε)) OPT(G)`, with one absolute
constant `c` in the `O(ε)`. -/
theorem lemma_6_8 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (H Y Yhat : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
        (Cstar : Setoid (Fin n)),
        0 < ε → ε ≤ 1 / 1000 → IsSpectralSparsifier ε (adjMat G) H →
        UniversalSubmod.CorrMatrix Y →
        (∀ Z : Matrix (Fin n) (Fin n) ℝ, UniversalSubmod.CorrMatrix Z →
          PsiTilde G (rescale ε H) Y ≤ PsiTilde G (rescale ε H) Z + ε ^ 2) →
        (∀ u v, u ≠ v → |Yhat u v - Y u v| ≤ ε / n) →
        IsOptimal G Cstar → 1 ≤ OPT G →
        pairSum (fun u v => (Yhat u v - adjMat G u v) ^ 2 + (Yhat u v - clusterMat Cstar u v) ^ 2)
          ≤ (1 + c * ε) * (OPT G : ℝ) := by sorry

end RobustCorrClust.Main
