-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_linearPath
-- name    : QAlgorithms.Papers.Independent.Support50.P17.linearPath
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:59:25.063248+00:00
-- url     : https://prove2.me/theorems/e4425cc3-a4e8-4f2c-8c3c-d37e72b82bdc
-- title:
--   Linear-path integral representation of relative entropy
-- statement:
--   Let $A\ge0$ and $B>0$ be square complex matrices on the same nonzero finite-dimensional Hilbert space. Their traces need not agree and $A$ may be singular. Put $\Delta=B-A$ and use natural spectral logarithms. The real scalar function $s\mapsto\operatorname{Re}\operatorname{Tr}[\Delta\log(A+s\Delta)]$ is integrable on $[0,1]$, and
--
--   $$
--   S(A\|B)=\operatorname{Re}\operatorname{Tr}(A-B)
--   +\operatorname{Re}\operatorname{Tr}[\Delta\log B]
--   -\int_0^1\operatorname{Re}\operatorname{Tr}[\Delta\log(A+s\Delta)]\,ds.
--   $$
--
--   At a zero eigenvalue the endpoint logarithm is assigned zero for this integrand; changing that single endpoint value does not change the integral. The entropy itself uses the zero-weight spectral convention.
--
--   This is the separately displayed linear specialization (12); it does not replace the deferred arbitrary-path assertion.
-- source:
--   Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, PDF p. 4, Lemma 1, explicit linear-path result (12)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF pp.4–5, Lemma 1, displayed linear-path identity (12), independently of
its under-specified arbitrary-path claim. A may be singular; equal trace is not assumed.
Integrability of the actual real scalar integrand is part of the conclusion. -/
theorem linearPath {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosDef) :
    let f : ℝ → ℝ := fun s =>
      ((B - A) * cfc Real.log (A + (s : ℂ) • (B - A))).trace.re
    IntegrableOn f (Set.Icc (0 : ℝ) 1) ∧
      relativeEntropy A B =
        (((A - B).trace.re + ((B - A) * cfc Real.log B).trace.re -
          ∫ s in Set.Icc (0 : ℝ) 1, f s : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
