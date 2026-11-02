-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_hilbert_stone_noncompact
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.hilbert_stone_noncompact
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:49:31.546489+00:00
-- url     : https://prove2.me/theorems/b1cdcd96-daf1-4509-91ca-c05045d9e533
-- title:
--   Proposition 3.21
-- statement:
--   If a complex Hilbert space $H$ has dimension greater than one, its closed-subspace Stone spectrum is not compact; in infinite dimension it is not locally compact:
--
--   $$\dim H>1\ \Longrightarrow\ Q(L(H))\text{ is noncompact},\qquad
--   \dim H=\infty\ \Longrightarrow\ Q(L(H))\text{ is not locally compact}.$$
--
--   This does not claim that every point lacks a compact neighbourhood: atomic quasipoints remain isolated.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 65, Proposition 3.21

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.21; de Groote, Observables I, PDF p./pp. 65.
-/
theorem hilbert_stone_noncompact {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hdim : 1 < Module.rank ℂ H) :
    ¬ CompactSpace (StoneSpectrum (ClosedSubmodule ℂ H)) ∧
      (¬ FiniteDimensional ℂ H → ¬ LocallyCompactSpace (StoneSpectrum (ClosedSubmodule ℂ H))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
