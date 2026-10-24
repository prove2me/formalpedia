-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_standardization
-- name    : QAlgorithms.Papers.Independent.Support50.P42.standardization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:14:32.706241+00:00
-- url     : https://prove2.me/theorems/226c219d-cec4-421a-882c-332435ec7946
-- title:
--   Near-power projection to exact standard singlets
-- statement:
--   Let $D>0$ and $\ell\ge0$ be integers and let $\epsilon>0$ satisfy $2^\ell\le D<(1+\epsilon)2^\ell$. Start with $D^{-1/2}\sum_{j=0}^{D-1}|j,j\rangle$. Projection onto the first $2^\ell$ Schmidt coordinates, with its orthogonal complement as failure, is a complete local measurement. Its success probability is
--
--   $$q=\frac{2^\ell}{D}>1-\epsilon,\qquad 0\le1-q<\epsilon.$$
--
--   The successful subnormalized density is $q$ times the normalized maximally entangled state of local rank $2^\ell$. Local unitaries convert that state exactly into $\ell$ standard singlets. If $D=2^\ell$, failure has probability zero and needs no normalization. This states the paper's finite standardization step using local ranks.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 7, §II: near-power standardization to exact singlets

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.7: exact successful conversion and the strict near-power probability
bounds. These are local ranks. At D=2^ell failure has downCount zero, and is never
normalized. Local unitaries put the successful state into ell standard singlets. -/
theorem standardization (D ell : ℕ) (hD : 0<D) (epsilon : ℝ)
    (he : 0<epsilon) (hlo : 2^ell≤D)
    (hhi : (D : ℝ)<(1+epsilon)*(2 : ℝ)^ell) :
    (trim D ell)ᴴ*trim D ell+(trimFailure D ell)ᴴ*trimFailure D ell=1 ∧
    pureDensity (rectAct (Matrix.kronecker (trim D ell) (trim D ell)) (uniformKet D))=
      (((2 : ℝ)^ell/D : ℝ) : ℂ) • pureDensity (uniformKet (2^ell)) ∧
    1-epsilon<(2 : ℝ)^ell/D ∧
    0≤1-(2 : ℝ)^ell/D ∧ 1-(2 : ℝ)^ell/D<epsilon ∧
    ∃ U V : Matrix.unitaryGroup (Fin (2^ell)) ℂ,
      conjSuperop (Matrix.kronecker (U : Op (Fin (2^ell))) (V : Op (Fin (2^ell))))
        (pureDensity (uniformKet (2^ell)))=singlets ell := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
