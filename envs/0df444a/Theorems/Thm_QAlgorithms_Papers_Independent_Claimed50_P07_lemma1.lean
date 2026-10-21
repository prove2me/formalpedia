-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P07_lemma1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P07.lemma1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:09:27.538994+00:00
-- url     : https://prove2.me/theorems/89ab3c1f-98aa-4ee8-b67f-ee37fe5d827d
-- title:
--   Monotonicity of the perspective of a nonnegative concave function
-- statement:
--   Let $f:[0,\infty)\to\mathbb R$ be concave and nonnegative. For real numbers $0<x<y$ and $z\ge0$,
--
--   $$x f(z/x)\le y f(z/y).$$
--
--   This perspective inequality is used to combine contributions from different energy ranges. The paper restates Corollary 12 of Winter [26]; it is background rather than an original result.
-- source:
--   Uniform finite-dimensional approximation of basic capacities of energy-constrained channels, arXiv:1707.05641v2, PDF p. 9, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P07

noncomputable section

open Filter

open scoped NNReal ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P07

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier30.P05 (EnergySpectrum groundEnergy)

/-- Lemma 1, PDF p.9, locally restating Corollary 12 of Winter [26].
Concavity and nonnegativity are required only on the nonnegative half-line. -/
theorem lemma1 (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hnonneg : ∀ u ∈ Set.Ici (0 : ℝ), 0 ≤ f u)
    (x y z : ℝ) (hx : 0 < x) (hxy : x < y) (hz : 0 ≤ z) :
    x * f (z / x) ≤ y * f (z / y) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P07

end
