-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P42_projective_injective_inclusion
-- name    : QAlgorithms.Papers.Independent.Intake100.P42.projective_injective_inclusion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:24:14.894855+00:00
-- url     : https://prove2.me/theorems/88d6a851-82cf-4e78-9198-06dfec2c0c9f
-- title:
--   Contractive change to projective domain and injective range
-- statement:
--   Let $\alpha$ be a uniform crossnorm family and $X,Y,V,W$ arbitrary normed spaces over the common real or complex field. Every bounded linear map $T:X\otimes_\alpha Y\to V\otimes_\alpha W$, regarded as the same algebraic linear map, is bounded from $X\otimes_\pi Y$ to $V\otimes_\varepsilon W$. The canonical inclusion is linear and contractive:
--
--   $$\|T\|_{[\pi,\varepsilon]}\le\|T\|_{[\alpha,\alpha]}\le\sup_{u\ne0}\frac{\|Tu\|_\pi}{\|u\|_\varepsilon}.$$
--
--   The last supremum is interpreted in $[0,\infty]$ and need not be finite. Restricting to finite operator tensors yields their canonical bounded inclusion and the same contractive comparison. A zero domain has only the zero map and gives zero suprema. The domain is projective and the range is injective, following the source's ratio and displayed inclusions.
-- source:
--   Restriction of Uniform Crossnorms, arXiv:2212.10780v2, PDF p. 6, Remark 4.2: change from alpha/alpha to projective/injective operator norms

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P42

open scoped TensorProduct ENNReal

open QAlgorithms.Papers.Independent.Next46.P02

universe u

variable {F : Type u} [RCLike F]

/-- PDF pp.6--7, Remark 4.2: the canonical identity on underlying linear maps
is a contractive inclusion from alpha/alpha to projective-domain/injective-range.
The reverse ratio in (*) remains extended-valued. The prose's isolated
[vee,wedge] is corrected to [wedge,vee], as fixed by its ratio and inclusions. -/
theorem projective_injective_inclusion (a : CrossnormFamily F) (ha : IsUniform a)
    (X Y V W : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    [NormedAddCommGroup V] [NormedSpace F V]
    [NormedAddCommGroup W] [NormedSpace F W] :
    (∀ T : TensorProduct F X Y →ₗ[F] TensorProduct F V W,
      BoundedIn (a.norm X Y) (a.norm V W) T →
      BoundedIn algebraicProjectiveNorm injectiveNorm T ∧
      extendedOperatorNorm algebraicProjectiveNorm injectiveNorm T < ⊤ ∧
      algebraicMapNorm algebraicProjectiveNorm injectiveNorm T ≤ algebraicMapNorm (a.norm X Y) (a.norm V W) T ∧
      extendedOperatorNorm algebraicProjectiveNorm injectiveNorm T ≤
        extendedOperatorNorm (a.norm X Y) (a.norm V W) T ∧
      extendedOperatorNorm (a.norm X Y) (a.norm V W) T ≤
        extendedOperatorNorm injectiveNorm algebraicProjectiveNorm T) ∧
    (∀ L : TensorProduct F (X →L[F] V) (Y →L[F] W),
      BoundedIn algebraicProjectiveNorm injectiveNorm (operatorAction L) ∧
      restrictedOperatorNorm algebraicProjectiveNorm injectiveNorm L ≤
        restrictedOperatorNorm (a.norm X Y) (a.norm V W) L) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P42

end
