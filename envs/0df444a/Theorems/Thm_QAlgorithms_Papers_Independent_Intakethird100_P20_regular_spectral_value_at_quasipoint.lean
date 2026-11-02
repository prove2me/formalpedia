-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_regular_spectral_value_at_quasipoint
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.regular_spectral_value_at_quasipoint
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:32:59.976726+00:00
-- url     : https://prove2.me/theorems/c2ecc49c-7394-47e3-bb99-8637b3ba6563
-- title:
--   rem-1.2
-- statement:
--   Let $M$ be Hausdorff, $\sigma$ a regular spectral family of open sets, and $x\in D(\sigma)$. If a quasipoint $\mathfrak B$ lies over $x$, meaning that the intersection of the closures of its open sets is $\{x\}$, then its spectral cut is nonempty and bounded below, and
--
--   $$\inf\{\lambda:\sigma(\lambda)\in\mathfrak B\}=f_\sigma(x).$$
--
--   The assertion only concerns quasipoints over admissible points, so it requires no globally real-valued cut for an unbounded family.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 14, rem-1.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- rem-1.2; de Groote, Observables I, PDF p./pp. 14.
-/
theorem regular_spectral_value_at_quasipoint {M : Type u} [TopologicalSpace M] [T2Space M]
    (E : ℝ → Opens M) (hE : IsRegularSpectralFamily E)
    (x : M) (hx : x ∈ admissibleDomain E)
    (B : StoneSpectrum (Opens M)) (hB : LiesOver B x) :
    {t | E t ∈ B.val}.Nonempty ∧ BddBelow {t | E t ∈ B.val} ∧
      sInf {t | E t ∈ B.val} = spectralCutInfimum (fun t => (E t : Set M)) x := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
