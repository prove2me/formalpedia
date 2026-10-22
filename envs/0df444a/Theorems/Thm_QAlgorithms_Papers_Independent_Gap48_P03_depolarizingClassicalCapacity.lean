-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_depolarizingClassicalCapacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.depolarizingClassicalCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:52:18.44183+00:00
-- url     : https://prove2.me/theorems/9c02b5c3-9bcd-48fc-b6b7-89b96af53b17
-- title:
--   Depolarizing channel: exact unassisted classical capacity
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. Here $S_{\min}$ is the infimum of output von Neumann entropy over all input states, $\nu_p$ is the supremum of the positive Schatten $p$-norm over those states, and $\chi^*$ is the supremum of the output Holevo information over all finite normalized input ensembles. Let $C_{\rm Shan}$ optimize the classical mutual information over all finite input ensembles and finite output POVMs, and define $C_{\rm ult}$ as the ordinary limit of $C_{\rm Shan}(\Delta_\lambda^{\otimes n})/n$. This limit exists and
--
--   $$C_{\rm ult}(\Delta_\lambda)=\chi^*(\Delta_\lambda)=C_{\rm Shan}(\Delta_\lambda)=\log d-S_{\min}(\Delta_\lambda),\qquad S_{\min}(\Delta_\lambda)=-a\log a-(d-1)b\log b,$$
--
--   where $a=\lambda+(1-\lambda)/d$ and $b=(1-\lambda)/d$. For every orthonormal basis and every positive block length $n$, its $d^n$ product pure states with uniform probabilities and the projective measurement in that same product basis are normalized valid encodings and measurements; their mutual information divided by $n$ equals $C_{\rm ult}$. Thus the capacity is attained by the basis strategy without assistance.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 7, Theorem 1 / abstract: exact unassisted classical capacity and basis strategy

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

/-- King quant-ph/0204172v2, PDF pp.1,4,6-7, Theorem 1, (9),(19),(23).
The Shannon block limit converges, and the concrete product basis strategy
attains the same information rate at every positive block length. -/
theorem depolarizingClassicalCapacity {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1) :
    ultimateClassicalCapacity (depolarizing d (1 - lam)) = holevoQuantity (depolarizing d (1 - lam)) ∧
    holevoQuantity (depolarizing d (1 - lam)) = quantumShannonCapacity (depolarizing d (1 - lam)) ∧
    quantumShannonCapacity (depolarizing d (1 - lam)) =
      Real.log d - (minimumOutputEntropy (depolarizing d (1 - lam))).toReal ∧
    (minimumOutputEntropy (depolarizing d (1 - lam))).toReal = depolarizingEntropy d lam ∧
    Tendsto (shannonBlockRate (depolarizing d (1 - lam))) atTop
      (nhds (ultimateClassicalCapacity (depolarizing d (1 - lam)))) ∧
    ∀ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ n : ℕ, 1 ≤ n →
      IsLaw (productBasisProb d n) ∧
      (∀ x, IsDensityMatrix (productBasisProjector (U : Matrix (Fin d) (Fin d) ℂ) n x)) ∧
      IsPOVM (productBasisProjector (U : Matrix (Fin d) (Fin d) ℂ) n) ∧
      productBasisInformation (depolarizing d (1 - lam)) (U : Matrix (Fin d) (Fin d) ℂ) n / n =
        ultimateClassicalCapacity (depolarizing d (1 - lam)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
