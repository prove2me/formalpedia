-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_localUnitaryInvariance
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.localUnitaryInvariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:57:54.809154+00:00
-- url     : https://prove2.me/theorems/bec7ca1e-9a2c-4607-9ce0-edfb61f99f63
-- title:
--   Output p-norm invariance under an arbitrary local input unitary
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. Let $\Psi$ be any completely positive trace-preserving map between arbitrary nonzero finite-dimensional complex matrix spaces; its input and output dimensions may differ. Let $\rho$ be any bipartite state on the depolarizing input and the input of $\Psi$, let $U$ be any unitary on the first factor, and set $\rho^\prime=(U\otimes I)\rho(U^*\otimes I)$. For every real $p\ge1$,
--
--   $$\|(\Delta_\lambda\otimes\Psi)(\rho)\|_p=\|(\Delta_\lambda\otimes\Psi)(\rho^\prime)\|_p.$$
--
--   The norm is the positive Schatten norm. There is no assumption that either marginal is diagonal; this is the invariance property used when choosing a convenient input basis.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 10, Lemma 7: invariance under a local unitary at the input

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

namespace QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0204172v2, PDF p.10, Lemma 7, (31).
The local input unitary is arbitrary; no diagonal-marginal assumption is present. -/
theorem localUnitaryInvariance {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1)
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (Psi : Superop A B) (hPsi : IsChannel Psi)
    (rho : Matrix (Fin d × A) (Fin d × A) ℂ) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (p : ℝ) (hp : 1 ≤ p) :
    schatten p (productChannel (depolarizing d (1 - lam)) Psi rho) =
      schatten p (productChannel (depolarizing d (1 - lam)) Psi
        (conjSuperop (Matrix.kronecker (U : Matrix (Fin d) (Fin d) ℂ) (1 : Matrix A A ℂ)) rho)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
