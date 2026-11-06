-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_D_13
-- name    : RollingProbeQN.Convex.lemma_D_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:19:41.313859+00:00
-- url     : https://prove2.me/theorems/78a234c7-a966-49c5-a309-9a70cc888f42
-- title:
--   Lemma D.13 — eigenvalue clipping is 2-stable in operator norm and nonexpansive in Frobenius norm
-- statement:
--   Let $L_1>0$.
--
--   1. If $H\in\mathcal Z$, $S$ is symmetric and $\|S-H\|_{\mathrm{op}}\le e$, then $\|\Pi_{\mathcal Z}(S)-H\|_{\mathrm{op}}\le2e$.
--   2. The same holds for clipping to the PSD cone, $S=U\operatorname{diag}(s_i)U^\top\mapsto U\operatorname{diag}(\max\{s_i,0\})U^\top$, when $H\succeq0$.
--   3. For symmetric $S,T$, $\|\Pi_{\mathcal Z}(S)-\Pi_{\mathcal Z}(T)\|_F\le\|S-T\|_F$.
--
--   Clipping restores feasibility of the curvature model at the cost of a factor $2$ in its error.
--
--   Differences from the source:
--   - encoding: ‖·‖op and ‖·‖F of matrices → the norm of Matrix.toEuclideanCLM and the square root of the sum of squared entries; reason: the same norms
--   - encoding: Π_Z clips the eigenvalues of a symmetric matrix to [0, L₁] → clipZ L₁, the functional calculus of t ↦ min (max t 0) L₁ (0 on non-symmetric input); reason: the same map on symmetric matrices, the only input it receives (reading R6)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma D.13, p. 42

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_InZ
import Definitions.Def_RollingProbeQN_Convex_clipZ

namespace RollingProbeQN.Convex

/-- **Lemma D.13 (Clipping is 2-stable in operator norm).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma D.13, p. 42: "If `H ∈ Z` and `‖S − H‖op ≤ e` for symmetric `S`, then
`‖Π_Z(S) − H‖op ≤ 2e`. The same conclusion holds for clipping to the PSD cone when `H ⪰ 0`. Also,
projection onto `Z` is nonexpansive in Frobenius norm."

Three clauses: the operator-norm bound for `Π_Z`; the same bound for the PSD clipping
`S ↦ U diag(max{s_i, 0}) U^T`; and `‖Π_Z(S) − Π_Z(T)‖_F ≤ ‖S − T‖_F` for symmetric `S, T`.

**Formalization Note.** The operator norm of a matrix is the norm of the continuous linear map
`Matrix.toEuclideanCLM`; the Frobenius norm is written out. The PSD clipping is the functional
calculus of `t ↦ max t 0`. `Π_Z` is applied to symmetric matrices, as on the page. -/
theorem lemma_D_13 {d : ℕ} {L₁ : ℝ} (hL₁ : 0 < L₁) :
    (∀ (H S : Matrix (Fin d) (Fin d) ℝ) (e : ℝ), InZ L₁ H → S.IsHermitian →
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (S - H)‖ ≤ e → ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (clipZ L₁ S - H)‖ ≤ 2 * e) ∧
    (∀ (H S : Matrix (Fin d) (Fin d) ℝ) (e : ℝ) (hS : S.IsHermitian), H.PosSemidef →
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (S - H)‖ ≤ e →
        ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (hS.cfc (fun t => max t 0) - H)‖ ≤ 2 * e) ∧
    (∀ S T : Matrix (Fin d) (Fin d) ℝ, S.IsHermitian → T.IsHermitian →
      Real.sqrt (∑ i, ∑ j, ((clipZ L₁ S - clipZ L₁ T) i j) ^ 2)
        ≤ Real.sqrt (∑ i, ∑ j, ((S - T) i j) ^ 2)) := by sorry

end RollingProbeQN.Convex
