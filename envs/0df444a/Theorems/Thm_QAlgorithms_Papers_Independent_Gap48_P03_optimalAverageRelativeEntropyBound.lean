-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_optimalAverageRelativeEntropyBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.optimalAverageRelativeEntropyBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:03:56.611687+00:00
-- url     : https://prove2.me/theorems/cbd3c032-1a9b-4a26-8889-a2246d2d1312
-- title:
--   Relative entropy bound at an actual optimal average
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. Let $\Psi$ be any completely positive trace-preserving map between arbitrary nonzero finite-dimensional complex matrix spaces; its input and output dimensions may differ. Let $\mathcal E=\{(\pi_i,\rho_i)\}$ be any normalized finite input ensemble attaining $\chi^*(\Psi)$, and put $\omega^*=\sum_i\pi_i\rho_i$. For every bipartite density matrix $\rho$ on the input of $\Delta_\lambda\otimes\Psi$,
--
--   $$D\!\left((\Delta_\lambda\otimes\Psi)(\rho)\,\middle\|\,\frac{I}{d}\otimes\Psi(\omega^*)\right)\le\chi^*(\Delta_\lambda)+\chi^*(\Psi).$$
--
--   Here $\chi^*$ is the supremum of finite-ensemble output Holevo information and $D$ is Umegaki relative entropy in nats, with value $+\infty$ on support failure. The reference is the actual average output of an attaining ensemble, which is the property required in the additivity argument.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 21, Lemma 12: relative entropy bound at an optimal average output

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

/-- King quant-ph/0204172v2, PDF p.21, Lemma 12, (105).
The reference is the actual average of a Holevo-attaining ensemble for Psi.
Output/reference normalization is concluded so the frozen Umegaki definition applies;
support failure retains infinity, and no desired bound is a hypothesis. -/
theorem optimalAverageRelativeEntropyBound {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1)
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (Psi : Superop A B) (hPsi : IsChannel Psi)
    (e : Ensemble A) (he : holevoScore Psi e = holevoQuantity Psi)
    (rho : Matrix (Fin d × A) (Fin d × A) ℂ) (hrho : IsDensityMatrix rho) :
    let output := productChannel (depolarizing d (1 - lam)) Psi rho
    let reference := Matrix.kronecker ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ))
      (Psi (ensembleAverage e))
    ∃ (houtput : IsDensityMatrix output) (hreference : IsDensityMatrix reference),
      QuantumLoss.umegakiEntropy output reference houtput hreference ≤
        ENNReal.ofReal (holevoQuantity (depolarizing d (1 - lam)) + holevoQuantity Psi) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
