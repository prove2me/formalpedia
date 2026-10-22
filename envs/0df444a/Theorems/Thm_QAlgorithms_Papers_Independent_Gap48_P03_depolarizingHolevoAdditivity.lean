-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_depolarizingHolevoAdditivity
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.depolarizingHolevoAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:53:07.368609+00:00
-- url     : https://prove2.me/theorems/62667a05-d8b7-40b5-b47a-9b85800d2491
-- title:
--   Strong Holevo additivity with an arbitrary companion
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. Let $\Psi$ be any completely positive trace-preserving map between arbitrary nonzero finite-dimensional complex matrix spaces; its input and output dimensions may differ. Here $S_{\min}$ is the infimum of output von Neumann entropy over all input states, $\nu_p$ is the supremum of the positive Schatten $p$-norm over those states, and $\chi^*$ is the supremum of the output Holevo information over all finite normalized input ensembles. Then
--
--   $$\chi^*(\Delta_\lambda\otimes\Psi)=\chi^*(\Delta_\lambda)+\chi^*(\Psi).$$
--
--   The tensor-channel optimization includes arbitrary entangled input ensembles. This evaluates the one-use Holevo quantity of the product channel.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 7, Theorem 2: strong Holevo additivity with an arbitrary companion channel

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

/-- King quant-ph/0204172v2, PDF p.7, Theorem 2, (24).
The companion is an arbitrary CPTP map, with positive input/output dimensions that may differ. -/
theorem depolarizingHolevoAdditivity {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1)
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (Psi : Superop A B) (hPsi : IsChannel Psi) :
    holevoQuantity (productChannel (depolarizing d (1 - lam)) Psi) =
      holevoQuantity (depolarizing d (1 - lam)) + holevoQuantity Psi := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
