-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_local_unitary_mixtures_preserve_sharing
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.local_unitary_mixtures_preserve_sharing
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:53:28.549867+00:00
-- url     : https://prove2.me/theorems/dac738b5-bd74-44a8-a67a-d3ec799657f1
-- title:
--   Theorem II.5: local-unitary mixtures preserve sharing
-- statement:
--   For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   Let the two local Hilbert spaces be nonzero and finite dimensional, and let $\rho$ be an $m$-$n$ sharable state. For any finite probability vector $(p_i)$ and local unitaries $U_i$ on $H_L$, $V_i$ on $H_R$,
--   $$\sum_i p_i(U_i\otimes V_i)\rho(U_i\otimes V_i)^\dagger\quad\text{is }m\text{-}n\text{ sharable}.$$
--   This is the class of local unitary mixtures specified by Eq.(4) and the proof.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 5, Theorem II.5: local-unitary mixtures preserve sharing

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Theorem II.5, Eq.(4), PDF p.5: the proof specifies product local unitaries.
The unrestricted word "unitaries" in the theorem sentence is interpreted through Eq.(4). -/
theorem local_unitary_mixtures_preserve_sharing {I J : Type*}
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (m n q : ℕ) (hm : 0 < m) (hn : 0 < n) (rho : Op (I × J))
    (hrho : IsDensityMatrix rho) (hshare : Sharable m n rho)
    (p : Fin q → ℝ) (hp : ∀ i, 0 ≤ p i) (hpSum : (∑ i, p i) = 1)
    (U : Fin q → Matrix.unitaryGroup I ℂ) (V : Fin q → Matrix.unitaryGroup J ℂ) :
    Sharable m n (∑ i, (p i : ℂ) • localConjugate (U i : Op I) (V i : Op J) rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
