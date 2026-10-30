-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_cb_decreasing_positive_attainment
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.cb_decreasing_positive_attainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:38:46.441168+00:00
-- url     : https://prove2.me/theorems/8bf499ff-4467-4e81-bc41-98b7b86f0374
-- title:
--   Corollary 14: positive input suffices for CB norm, q >= p
-- statement:
--   Let $\Phi:M_m\to M_n$ be CP and $1\le p\le q\le\infty$, with $m,n\ge1$. At every $d\ge1$ there is a positive semidefinite $X\in M_d\otimes M_m$ satisfying
--
--   $$\|X\|_{(p,q)}=1,\qquad\|\Phi\|_{\mathrm{CB},q\to p}=\|(\mathrm{id}_d\otimes\Phi)(X)\|_{(p,p)}.$$
--
--   Thus positive input suffices for the CB supremum, using the common outer exponent $p$ of (3.5). The maximizer can already be chosen at $d=1$ by Theorem 13(a) and Corollary 6. This pins the corollary's amplification notation to its intended operator-space norms.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 21, Corollary 14: positive input suffices for CB norm, q >= p

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

/-- Corollary 14, PDF pp.21–22, interpreted using (3.5), t=p.
At every positive finite outer dimension a PSD input attains the full CB supremum;
the definition is not an ordinary Schatten norm on the entire tensor product. -/
theorem cb_decreasing_positive_attainment {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (d : ℕ) (hd : 0 < d)
    (q p : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q)
    (Phi : (Mat I →ₗ[ℂ] Mat J)) (hPhi : Entanglement.IsCompletelyPositive Phi) :
    ∃ X : Mat (Fin d × I), X.PosSemidef ∧ mixedNorm p q X = 1 ∧
      cbSize q p Phi = ENNReal.ofReal (mixedNorm p p (idTensorSuperop Phi X)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
