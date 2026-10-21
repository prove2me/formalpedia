-- Prove2me | Theorems.Thm_TVSDP_PolyOpt_lemma_3a
-- name    : TVSDP.PolyOpt.lemma_3a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:04.103231+00:00
-- url     : https://prove2.me/theorems/fe719f73-ed81-4154-bdb3-aa519fa22673
-- title:
--   Lemma 3(a), p. 12 — $\mathcal M_v$ preserves positive semidefiniteness: $M(t)\succeq0$ a.e. $\Rightarrow$ $\mathcal M_vM(t)\succeq0$ for all $t\in[0,1]$
-- statement:
--   Let $M\in\mathbf S^m$, that is, $M:[0,1]\to\mathbb R^{m\times m}$ with $M(t)$ symmetric for every $t\in[0,1]$ and with bounded entries, and assume the entries of $M$ are measurable. If $M(t)\succeq0$ for almost every $t\in[0,1]$, then for every $v\in\mathbb N$
--
--   $$\mathcal M_v M(t)\succeq 0\qquad\text{for every } t\in[0,1],$$
--
--   where $\mathcal M_v$ acts entrywise (Definition 3, Remark 1).
--
--   In the proof of Theorem 4 this transfers the strict feasibility margin of a solution to its mollification.
--
--   **Formalization Note** Measurability of the entries of $M$ is added: the definition of $\mathbf S^m$ on p. 2 lists only symmetry and boundedness, but $\mathcal M_vM$ is an integral of $M$, so the paper uses it implicitly.
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, p. 12, Lemma 3(a)

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Setting
import Definitions.Def_TVSDP_PolyOpt_Mollifier

namespace TVSDP.PolyOpt

open MeasureTheory

/-- Lemma 3(a), p. 12: if `M ∈ S^m` (measurable) satisfies `M(t) ⪰ 0` for almost every `t ∈ [0,1]`,
then `𝓜_v M(t) ⪰ 0` for every `t ∈ [0,1]` and every `v ∈ ℕ`. -/
theorem lemma_3a {m : ℕ} (M : ℝ → Matrix (Fin m) (Fin m) ℝ) (hM : M ∈ Sm m)
    (hmeas : ∀ j k, Measurable fun s => M s j k)
    (hpsd : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)), (M t).PosSemidef) (v : ℕ) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, (MvMat v M t).PosSemidef := by sorry

end TVSDP.PolyOpt
