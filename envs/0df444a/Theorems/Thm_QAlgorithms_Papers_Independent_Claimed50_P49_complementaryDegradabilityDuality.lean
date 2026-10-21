-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_complementaryDegradabilityDuality
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.complementaryDegradabilityDuality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:02:16.056445+00:00
-- url     : https://prove2.me/theorems/6296bad4-2e75-4755-9360-05ee2cee1841
-- title:
--   Anti-degradability and degradability of a true complement
-- statement:
--   Let $E:A\to A$ and $F:A\to B$ be trace-class CPTP channels forming a true complementary pair through one pure Stinespring isometry. Allow the two output Hilbert spaces to differ. Then
--
--   $$E\text{ is anti-degradable in some physical representation}\iff\exists T:B\to A\text{ CPTP},\quad T\circ F=E.$$
--
--   Equivalently, $F$ is ordinarily degradable with its true complement $E$. All equalities hold on every density. The existential physical representation on the left is essential; no recovery from every preselected mixed weak complement is claimed.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 4, §1, after (1.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section 1, PDF p.4: existential physical anti-degradability is equivalent
to ordinary degradability of a true complement. The recovery predicate accepts
heterogeneous outputs; no converse for an arbitrary fixed mixed pair is asserted. -/
theorem complementaryDegradabilityDuality {I J : Type} [Nonempty I]
    (E : Operation I I) (F : Operation I J) (hpair : TrueComplementary E F) :
    HasAntiRepresentation E ↔ WeaklyDegradable F E := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
