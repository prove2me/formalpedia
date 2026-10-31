-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_trace_averaging
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.trace_averaging
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:42:12.098864+00:00
-- url     : https://prove2.me/theorems/f44c1fe6-c6f6-41fe-bf4c-9eac275505ea
-- title:
--   Proposition 5.2: trace averaging gives central/intertwining maps
-- statement:
--   Let $A$ be a finite-dimensional unital algebra over an algebraically closed field $F$, let $t$ be a nondegenerate linear trace, and let $(b_i)$ and $(b_i^*)$ be trace-dual bases. For $a\in A$ and an $F$-linear map $\phi:M\to N$ between unital $A$-modules with compatible $F$-scalars, put
--
--   $$[a]=\sum_i b_iab_i^*,\qquad [\phi](v)=\sum_i b_i\cdot\phi(b_i^*\cdot v).$$
--
--   Then $[a]$ is central, $[\phi]$ is an $A$-module homomorphism, and both averages are unchanged on replacing the basis by any other basis and its actual trace-dual. The theorem supplies canonical central and intertwining maps.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 40, Proposition 5.2: trace averaging gives central/intertwining maps

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Centrality, intertwining, and independence of both averages, PDF p.40, Proposition 5.2. -/
theorem trace_averaging (F A M N I : Type*) [Field F] [IsAlgClosed F]
    [Ring A] [Algebra F A] [FiniteDimensional F A] [Fintype I] [DecidableEq I]
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    [Module A M] [Module A N] [IsScalarTower F A M] [IsScalarTower F A N]
    (t : A →ₗ[F] F) (_htrace : ∀ a b : A, t (a * b) = t (b * a))
    (_hnd : TraceNondegenerate (fun a => t a))
    (b c : Module.Basis I F A) (_hdual : IsTraceDualBasis t b c) (phi : M →ₗ[F] N) :
    (∀ a z : A, z * algebraAverage b c a = algebraAverage b c a * z) ∧
    (∀ (J : Type*) [Fintype J] [DecidableEq J] (d f : Module.Basis J F A),
      IsTraceDualBasis t d f → ∀ a : A, algebraAverage b c a = algebraAverage d f a) ∧
    (∃ f : M →ₗ[A] N, ∀ m : M, f m = moduleAverage b c phi m) ∧
    (∀ (J : Type*) [Fintype J] [DecidableEq J] (d f : Module.Basis J F A),
      IsTraceDualBasis t d f → ∀ m : M, moduleAverage b c phi m = moduleAverage d f phi m) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
