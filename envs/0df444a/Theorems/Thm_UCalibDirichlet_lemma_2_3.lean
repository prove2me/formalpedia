-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_2_3
-- name    : UCalibDirichlet.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:30.375062+00:00
-- url     : https://prove2.me/theorems/06a4ded0-29b0-475f-af21-1507a6cce264
-- title:
--   Lemma 2.3 — $V_F(T)+\Lambda_F(\mathbf 1)\le C_1K\log(eT)L_F(T)$
-- statement:
--   There is a universal constant $C_1$ such that for every $K\ge2$, every $T\ge1$ and every normalized, finite, continuous, convex $F:\Delta_K\to\mathbb R$,
--   $$V_F(T)+\Lambda_F(\mathbf 1)\le C_1\,K\log(eT)\,L_F(T).$$
--
--   This bounds the BTPL regret of Algorithm 1 (Lemma 1.5) by the Bernstein complexity $L_F(T)$.
--
--   Differences from the source:
--   - encoding: a universal C₁ → ∃ C₁ : ℝ quantified before K, T and F; reason: universal means independent of K, T and F
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 2.3, display (20), p.13

import Mathlib
import Definitions.Def_UCalibDirichlet_Lam
import Definitions.Def_UCalibDirichlet_VF
import Definitions.Def_UCalibDirichlet_LF
import Definitions.Def_UCalibDirichlet_IsNormalized

namespace UCalibDirichlet

/-- **Lemma 2.3 (bounding BTPL regret).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), Lemma 2.3, display (20), p.13: "For `K ≥ 2`, `T ≥ 1`, and normalized finite continuous
convex `F`, `V_F(T) + Λ_F(𝟏) ≤ C₁ K log(eT) L_F(T)` (20) for a universal `C₁`."

**Formalization Note.** "Universal" is one `∃ C₁` quantified before `K`, `T` and `F`. "Normalized"
is (4) (`IsNormalized`); "finite continuous convex" is a real-valued `F` continuous and convex on
`Δ_K`. `log` is the natural logarithm. (The proof, p.31, gives `C₁ = 139`; the statement only
asserts a universal constant.) -/
theorem lemma_2_3 : ∃ C₁ : ℝ, ∀ (K : ℕ), 2 ≤ K → ∀ (T : ℕ), 1 ≤ T →
    ∀ F : (Fin K → ℝ) → ℝ, ContinuousOn F (stdSimplex ℝ (Fin K)) →
      ConvexOn ℝ (stdSimplex ℝ (Fin K)) F → IsNormalized F →
        VF F T + Lam F (fun _ => 1) ≤ C₁ * K * Real.log (Real.exp 1 * T) * LF F T := by sorry

end UCalibDirichlet
