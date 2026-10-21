-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_covariant_seed_normalization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.covariant_seed_normalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:28:52.121671+00:00
-- url     : https://prove2.me/theorems/f7fe2d1c-4b40-488a-8eec-c6ee151a1eea
-- title:
--   Covariant seed normalization is equivalent to total seed trace d
-- statement:
--   Let d>0 and let Π_j be any finite family of positive operators on output⊗input, with both dimensions d. Use independent normalized SU(d) Haar measures and counting measure on j. Its covariant density Π_(j,U,V)=(U⊗V)Π_j(U⊗V)† has integral (∑_j Tr Π_j)I/d². Consequently it is a physical tester if and only if ∑_j Tr Π_j=d. Zero seed effects are allowed; none is divided by its trace.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 3, (25); p.2 (24)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF pp.2–3, (24)–(25): arbitrary positive seeds give a normalized covariant
tester exactly when their traces sum to d; zero seed effects need not be divided by. -/
theorem covariant_seed_normalization {d : ℕ} (hd : 0 < d)
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (P : J → Op (ChoiBasis d)) (hP : ∀ j, (P j).PosSemidef) :
    (∫ z, covariant P z ∂(Measure.count.prod (haar.prod haar))) =
      ((∑ j, (P j).trace) / (d : ℂ)^2) • (1 : Op (ChoiBasis d)) ∧
    (IsTesterDensity (Measure.count.prod (haar.prod haar)) (covariant P) ↔
      ∑ j, (P j).trace = (d : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
