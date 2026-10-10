-- Prove2me | Theorems.Thm_ShortestGCS_Relax_remark_7_5
-- name    : ShortestGCS.Relax.remark_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:51.220542+00:00
-- url     : https://prove2.me/theorems/a62df913-0d99-46fa-a4b5-58a664e60e76
-- title:
--   Remark 7.5, p. 14 — if 𝒴 ⊆ [0, 1]ᵐ, every point of 𝒴 ∩ {0, 1}ᵐ is an extreme point of 𝒴
-- statement:
--   Let $\mathcal Y \subseteq [0, 1]^m$. Then every $y \in \mathcal Y$ whose coordinates all lie in $\{0, 1\}$ is an extreme point of $\mathcal Y$:
--
--   $$
--   y \in \mathcal Y \cap \{0, 1\}^m \implies y \in \operatorname{ext}\mathcal Y .
--   $$
--
--   Combined with Lemma 7.4 this says that the relaxation $\mathcal S'$ is exact at all binary points of such a $\mathcal Y$, which is the setting of the first-level Reformulation-Linearization Technique for mixed-binary bilinear programs.
--
--   **Formalization Note** Only the first clause of the remark is stated; its second clause is Lemma 7.4 at these points. No convexity of $\mathcal Y$ is needed.
-- source:
--   arXiv:2101.11565v5, Remark 7.5, p. 14

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

/-- Remark 7.5, arXiv:2101.11565v5, p. 14: if `𝒴 ⊆ [0, 1]ᵐ`, every `y ∈ 𝒴 ∩ {0, 1}ᵐ` is an extreme point of
`𝒴`. -/
theorem remark_7_5 {m : ℕ} (Y : Set (Fin m → ℝ)) (hY : Y ⊆ {y | ∀ i, y i ∈ Set.Icc (0 : ℝ) 1}) :
    ∀ y ∈ Y, (∀ i, y i = 0 ∨ y i = 1) → y ∈ Set.extremePoints ℝ Y := by sorry

end ShortestGCS.Relax
