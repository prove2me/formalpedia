-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_logarithmDerivativeBound
-- name    : QAlgorithms.Papers.Independent.Support50.P17.logarithmDerivativeBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:02:03.000161+00:00
-- url     : https://prove2.me/theorems/8411d55a-5575-472b-82f9-c63c2453d2fa
-- title:
--   Loewner bound for the logarithmic derivative map
-- statement:
--   Let $a,b>0$ be matrices on the same nonzero finite-dimensional complex Hilbert space with $\operatorname{Tr}a=\operatorname{Tr}b$. Let $t=\tfrac12\|b-a\|_1$ and let $\gamma\ge0$ satisfy $a\ge\gamma I$ in Loewner order. Define the actual logarithmic derivative map by its convergent resolvent integral
--
--   $$
--   \mathcal T_b(D)=\int_0^\infty(b+sI)^{-1}D(b+sI)^{-1}\,ds.
--   $$
--
--   For $D=b-a$, each complex matrix entry of the integrand is integrable, and
--
--   $$
--   \mathcal T_b(b-a)\le\frac{t}{\gamma+t}I.
--   $$
--
--   The inequality means the difference of its right and left sides is positive semidefinite. If $\gamma=t=0$, the quotient is interpreted as zero; then $a=b$ and both sides are zero.
--
--   This supplies the operator estimate used in the sharp entropy bound; no order-preserving map is supplied as an unrelated parameter.
-- source:
--   Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, PDF p. 6, Lemma 3: logarithmic-derivative operator bound (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF pp.6–7, Lemma 3, (14): actual logarithmic-derivative operator bound.
Convergence of each resolvent entry is concluded, not inserted as an extra hypothesis.
Loewner order is positivity of the difference; gamma=t=0 uses the valid value 0/0=0. -/
theorem logarithmDerivativeBound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (a b : Matrix I I ℂ) (ha : a.PosDef) (hb : b.PosDef)
    (htrace : a.trace = b.trace) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hlower : (a - (gamma : ℂ) • (1 : Matrix I I ℂ)).PosSemidef) :
    let t := traceDistance b a
    (∀ i j : I, IntegrableOn (fun s => resolventIntegrand b (b - a) s i j)
      (Set.Ioi (0 : ℝ))) ∧
    (((t / (gamma + t) : ℝ) : ℂ) • (1 : Matrix I I ℂ) -
      logarithmDerivativeMap b (b - a)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
