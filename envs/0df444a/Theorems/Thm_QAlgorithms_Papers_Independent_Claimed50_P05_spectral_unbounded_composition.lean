-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_spectral_unbounded_composition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.spectral_unbounded_composition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:23:59.700981+00:00
-- url     : https://prove2.me/theorems/23b678fc-2a3c-4db6-9b5e-e2d3f647ced7
-- title:
--   §7.3, unnumbered: universal composition rule
-- statement:
--   Let $A$ be a closed densely defined normal operator, self-adjoint in the real case, and let $f,g:k\to k$ be arbitrary finite-valued Borel functions. Using the unique associated Borel calculi,
--
--   $$g(f(A))=(g\circ f)(A).$$
--
--   No boundedness of $A$, $f$, $g$, or $f(A)$ is assumed. Equality is equality of full operator graphs, including domains.
--
--   This is the universal unbounded composition rule.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 35, §7.3, unnumbered: universal composition rule

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Section 7.3, PDF p.35: universal composition for finite Borel f and g; no boundedness assumptions. -/
theorem spectral_unbounded_composition (A : Relation H) (hA : SpectralAdmissible (k := k) A)
    (f g : Symbol k k) :
    spectralValue (spectralValue A f) g = spectralValue A (compose g f.val f.property) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
