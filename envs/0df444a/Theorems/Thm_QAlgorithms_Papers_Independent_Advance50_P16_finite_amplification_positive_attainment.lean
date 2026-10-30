-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_finite_amplification_positive_attainment
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.finite_amplification_positive_attainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:37:15.514628+00:00
-- url     : https://prove2.me/theorems/917798e5-a80c-46a1-89a4-3162fd361d61
-- title:
--   Theorem 12: positivity at each finite CB amplification, q <= p
-- statement:
--   Let $\Phi:M_m\to M_n$ be complex-linear CP, $m,n\ge1$, and let $1\le q\le p\le\infty$. At every prescribed finite ancillary dimension $d\ge1$, there is $X\ge0$ with $\|X\|_{(q,q)}=1$ such that
--
--   $$\|\mathrm{id}_d\otimes\Phi\|_{(q,q)\to(q,p)}=\|\mathrm{id}_d\otimes\Phi\|^+_{(q,q)\to(q,p)}=\|(\mathrm{id}_d\otimes\Phi)(X)\|_{(q,p)}.$$
--
--   The outer exponent is $q$ on both sides. This is finite-amplification attainment; it does not assert that a finite ancillary dimension attains the global CB supremum.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 20, Theorem 12: positivity at each finite CB amplification, q <= p

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Theorem 12, PDF pp.20–21: each prescribed finite amplification has a PSD maximizer. -/
theorem finite_amplification_positive_attainment {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (d : ℕ) (hd : 0 < d)
    (q p : ℝ≥0∞) (hq : 1 ≤ q) (hqp : q ≤ p)
    (Phi : (Mat I →ₗ[ℂ] Mat J)) (hPhi : Entanglement.IsCompletelyPositive Phi) :
    amplificationSize d q q p Phi = positiveAmplificationSize d q q p Phi ∧
    ∃ X : Mat (Fin d × I), X.PosSemidef ∧ mixedNorm q q X = 1 ∧
      amplificationSize d q q p Phi = ENNReal.ofReal (mixedNorm q p (idTensorSuperop Phi X)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
