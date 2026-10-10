-- Prove2me | Theorems.Thm_StochGradTrack_Const_lemma_5
-- name    : StochGradTrack.Const.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:22.369975+00:00
-- url     : https://prove2.me/theorems/2f262096-3393-438a-9f88-9767b91a6760
-- title:
--   Lemma 5, p. 421 — for nonnegative irreducible S ∈ ℝ^{3×3} with s_ii < λ*, ρ(S) < λ* iff det(λ*I − S) > 0
-- statement:
--   Let $S=[s_{ij}]\in\mathbb R^{3\times3}$ be nonnegative and irreducible, and let $\lambda^*>0$ satisfy $s_{ii}<\lambda^*$ for $i=1,2,3$. Then
--   $$\rho(S)<\lambda^*\iff\det(\lambda^*\mathbf I-S)>0,$$
--   where $\rho(S)$ is the spectral radius (the largest modulus of a complex eigenvalue).
--
--   The lemma turns the condition $\rho(\mathbf A)<1$ for the $3\times3$ matrix of (21) into an inequality on a determinant, which can be checked from the entries.
--
--   **Formalization Note.** Irreducibility is Mathlib's `Matrix.IsIrreducible`: entrywise nonnegative with a strongly connected digraph of positive entries. The spectral radius is taken over $\mathbb C$, of the complexified matrix, as an extended nonnegative real; over $\mathbb R$ complex eigenvalues would be missed.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Lemma 5, p. 421 (proof in App. 7.2)

import Mathlib
import Definitions.Def_StochGradTrack_Const_Matrix

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem lemma_5 (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.IsIrreducible) (lam : ℝ)
    (hlam : 0 < lam) (hdiag : ∀ i, S i i < lam) :
    spectralRadius ℂ (S.map (algebraMap ℝ ℂ)) < ENNReal.ofReal lam ↔
      0 < (lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) - S).det := by sorry

end StochGradTrack.Const
