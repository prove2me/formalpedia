-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_bounded_approximately_affine_continuity
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.bounded_approximately_affine_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:54:10.142232+00:00
-- url     : https://prove2.me/theorems/2f861671-5d77-4249-95ce-c65dd242511f
-- title:
--   Proposition VI.1: bounded approximately affine function continuity
-- statement:
--   Let $H$ be any complete complex Hilbert space, and let $\mathcal S(H)$ be its positive trace-class operators of trace one, represented using a chosen Hilbert basis. Let $f:\mathcal S(H)\to\mathbb C$ be bounded and suppose that, for every pair of states and every $t\in[0,1]$,
--
--   $$|f((1-t)\rho+t\sigma)-(1-t)f(\rho)-tf(\sigma)|\le h_2(t),$$
--
--   where $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with $0\log0=0$. Put $M=\sup_{\omega\in\mathcal S(H)}|f(\omega)|$. For every pair $\rho,\sigma$, writing $\varepsilon=\|\rho-\sigma\|_1/(2+\|\rho-\sigma\|_1)$,
--
--   $$|f(\rho)-f(\sigma)|\le2h_2(\varepsilon)+4\varepsilon M.$$
--
--   The nuclear norm is the actual unhalved trace norm. A supplied pair makes the bounded supremum nonempty. This continuity estimate applies without a finite-dimensional or separability assumption.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 9, Proposition VI.1: bounded approximately affine function continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Proposition VI.1, PDF pp.9–10: bounded approximately affine complex functions
on states of an arbitrary Hilbert space. The trace norm is the accepted nuclear norm;
no finite-dimensional or separability restriction is imposed. -/
theorem bounded_approximately_affine_continuity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {J : Type*} (b : HilbertBasis J ℂ H)
    (f : QAlgorithms.Papers.Independent.Dependency50.P13.State b → ℂ)
    (hbounded : BddAbove (Set.range (fun rho => ‖f rho‖)))
    (haffine : ApproximatelyAffine b f)
    (rho sigma : QAlgorithms.Papers.Independent.Dependency50.P13.State b) :
    let d := QAlgorithms.Papers.Independent.Dependency50.P13.traceNormValue (rho.1.1 - sigma.1.1)
    let e := d / (2 + d)
    let M := sSup (Set.range (fun omega => ‖f omega‖))
    ‖f rho - f sigma‖ ≤ 2 * binEntropy2 e + 4 * e * M := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
