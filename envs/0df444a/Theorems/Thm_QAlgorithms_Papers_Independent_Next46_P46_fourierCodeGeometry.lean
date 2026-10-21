-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P46_fourierCodeGeometry
-- name    : QAlgorithms.Papers.Independent.Next46.P46.fourierCodeGeometry
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:06:02.853454+00:00
-- url     : https://prove2.me/theorems/6af5f94a-8a9c-42f7-a60d-a4c2ba13afcd
-- title:
--   Fourier code spans and blockwise unbiased overlap
-- statement:
--   Let $L,M,S>0$, let $T$ be a set of word labels, and assign a vector $w_x$ in a finite Hilbert space to each label. Suppose codebooks $u^{lms}$ cover exactly $T$, and, for each fixed $l$, the vectors $v_{lms}=w_{u^{lms}}$ form an orthonormal family. Define
--
--   $$
--   f_{lmt}=\frac1{\sqrt S}\sum_{s=0}^{S-1}e^{2\pi i st/S}v_{lms}.
--   $$
--
--   For each $l$, the transformed family is orthonormal and spans the same space $Q_l$ as the original family. Its exact overlaps are
--
--   $$
--   \langle v_{lm's'},f_{lmt}\rangle=
--   \begin{cases}S^{-1/2}e^{2\pi i s't/S},&m'=m,\\0,&m'\ne m.\end{cases}
--   $$
--
--   Moreover, the span of all transformed code vectors equals $\operatorname{span}\{w_x:x\in T\}$. For the source's words this is the image under $W^{\otimes n}$ of the typical basis span.
--
--   Thus the bases are unbiased within each message block. For $M>1$ they are not globally mutually unbiased in dimension $MS$. This algebra makes no coding-performance assertion.
-- source:
--   Relating quantum privacy and quantum coherence: an operational approach, arXiv:quant-ph/0307053v1, PDF p. 4, Fourier-twisted code geometry

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

/-- arXiv:quant-ph/0307053v1, PDF p.4: Fourier code geometry, with span coverage.
SOURCE CORRECTION: 'mutually unbiased' is blockwise: cross-message overlaps vanish;
for the same message the magnitude is 1/sqrt(S), not 1/sqrt(MS).
No reliability, decoupling, or every-l,t coding-performance assertion follows. -/
theorem fourierCodeGeometry {H X : Type} [Fintype H] [Nonempty H]
    {l m s : ℕ} (hl : 0 < l) (hm : 0 < m) (hs : 0 < s)
    (base : X → Vec H) (typical : Set X)
    (u : Fin l → Fin m × Fin s → X)
    (hcover : ∀ x, x ∈ typical ↔ ∃ a j, u a j = x)
    (hv : ∀ a, Orthonormal ℂ (fun j => base (u a j))) :
    (∀ a, Orthonormal ℂ (fourierCode (fun j => base (u a j))) ∧
      Submodule.span ℂ (Set.range (fourierCode (fun j => base (u a j)))) =
        Submodule.span ℂ (Set.range (fun j => base (u a j))) ∧
      ∀ mt mj : Fin m × Fin s,
        inner ℂ (base (u a mj)) (fourierCode (fun j => base (u a j)) mt) =
          if mj.1 = mt.1 then fourierCoefficient s mt.2 mj.2 else 0) ∧
    Submodule.span ℂ (⋃ a, Set.range (fourierCode (fun j => base (u a j)))) =
      Submodule.span ℂ (base '' typical) := by sorry

end QAlgorithms.Papers.Independent.Next46.P46

end
