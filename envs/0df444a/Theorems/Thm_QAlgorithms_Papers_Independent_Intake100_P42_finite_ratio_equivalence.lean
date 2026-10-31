-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P42_finite_ratio_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P42.finite_ratio_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:26:30.003006+00:00
-- url     : https://prove2.me/theorems/11dc2fcd-a6f8-441b-b851-165baa48b3f5
-- title:
--   Finite extreme ratio implies the full norm sandwich and equivalence
-- statement:
--   Let $\alpha$ be any uniform crossnorm family, and $X,Y$ arbitrary normed spaces over the same real or complex field. Suppose the extended supremum
--
--   $$\gamma:=\sup_{0\ne u\in X\otimes Y}\frac{\|u\|_\pi}{\|u\|_\varepsilon}<\infty.$$
--
--   Then every algebraic tensor $u$ satisfies
--
--   $$\|u\|_\varepsilon\le\|u\|_\alpha\le\|u\|_\pi\le\gamma\|u\|_\varepsilon,$$
--
--   and both further suprema are finite:
--
--   $$\sup_{u\ne0}\frac{\|u\|_\pi}{\|u\|_\alpha}<\infty,\qquad\sup_{u\ne0}\frac{\|u\|_\alpha}{\|u\|_\varepsilon}<\infty.$$
--
--   The three norms are pairwise equivalent, expressed by positive finite two-sided bounds for the canonical identities. Gamma is computed from the displayed ratio, not supplied independently. On a zero tensor space gamma is zero and all norms vanish, while equivalence still admits positive constants. Finite dimension and completeness are not hypotheses.
-- source:
--   Restriction of Uniform Crossnorms, arXiv:2212.10780v2, PDF p. 8, Section 5, unnumbered: bounded projective/injective ratio forces equivalence of every uniform crossnorm

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P42

open scoped TensorProduct ENNReal

open QAlgorithms.Papers.Independent.Next46.P02

universe u

variable {F : Type u} [RCLike F]

/-- PDF p.8, Section 5: finite extreme ratio forces the full norm sandwich,
both finite-ratio assertions, and equivalence. Gamma is the computed supremum,
not independent data. Zero factors are allowed; then gamma is zero. No Pisier
isometry or claimed gamma=1 consequence is included. -/
theorem finite_ratio_equivalence (a : CrossnormFamily F) (ha : IsUniform a)
    (X Y : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    (hfinite : ratioSup (algebraicProjectiveNorm (F := F) (X := X) (Y := Y)) injectiveNorm < ⊤) :
    let gamma := ratioSup (algebraicProjectiveNorm (F := F) (X := X) (Y := Y)) injectiveNorm
    (∀ t : TensorProduct F X Y,
      injectiveNorm t ≤ a.norm X Y t ∧
      a.norm X Y t ≤ algebraicProjectiveNorm t ∧
      algebraicProjectiveNorm t ≤ gamma.toReal * injectiveNorm t) ∧
    ratioSup algebraicProjectiveNorm (a.norm X Y) < ⊤ ∧
    ratioSup (a.norm X Y) injectiveNorm < ⊤ ∧
    NormEquivalent (injectiveNorm (F := F) (X := X) (Y := Y)) algebraicProjectiveNorm ∧
    NormEquivalent injectiveNorm (a.norm X Y) ∧
    NormEquivalent (a.norm X Y) algebraicProjectiveNorm := by sorry

end QAlgorithms.Papers.Independent.Intake100.P42

end
