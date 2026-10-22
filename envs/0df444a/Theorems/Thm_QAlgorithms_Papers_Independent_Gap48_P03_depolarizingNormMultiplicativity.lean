-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_depolarizingNormMultiplicativity
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.depolarizingNormMultiplicativity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:54:13.023898+00:00
-- url     : https://prove2.me/theorems/e2a7bd2d-33b1-4105-bad5-2e5dd877d03f
-- title:
--   Real-p norm multiplicativity and minimum entropy additivity
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. Let $\Psi$ be any completely positive trace-preserving map between arbitrary nonzero finite-dimensional complex matrix spaces; its input and output dimensions may differ. Here $S_{\min}$ is the infimum of output von Neumann entropy over all input states, $\nu_p$ is the supremum of the positive Schatten $p$-norm over those states, and $\chi^*$ is the supremum of the output Holevo information over all finite normalized input ensembles. For every real $p\ge1$,
--
--   $$\nu_p(\Delta_\lambda\otimes\Psi)=\nu_p(\Delta_\lambda)\nu_p(\Psi),\qquad S_{\min}(\Delta_\lambda\otimes\Psi)=S_{\min}(\Delta_\lambda)+S_{\min}(\Psi).$$
--
--   Both optimizations on the product include all bipartite states. The norm claim includes noninteger exponents and $p=1$, and makes no assertion at $p=\infty$.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 8, Theorem 3: all-real-p maximal-output-norm multiplicativity and minimum-entropy additivity

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

/-- King quant-ph/0204172v2, PDF p.8, Theorem 3, (25)-(26).
Both real-p multiplicativity (including p=1) and minimum-entropy additivity are stated. -/
theorem depolarizingNormMultiplicativity {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1)
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (Psi : Superop A B) (hPsi : IsChannel Psi) :
    (∀ p : ℝ, 1 ≤ p → maximumOutputPNorm (productChannel (depolarizing d (1 - lam)) Psi) p =
      maximumOutputPNorm (depolarizing d (1 - lam)) p * maximumOutputPNorm Psi p) ∧
    (minimumOutputEntropy (productChannel (depolarizing d (1 - lam)) Psi)).toReal =
      (minimumOutputEntropy (depolarizing d (1 - lam))).toReal + (minimumOutputEntropy Psi).toReal := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
