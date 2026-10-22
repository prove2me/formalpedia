-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_clockIntermediateDecomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.clockIntermediateDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:00:59.155068+00:00
-- url     : https://prove2.me/theorems/580a18cb-5318-4dda-abe4-cd4faaf44e1f
-- title:
--   Clock decomposition through the intermediate channel
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. Define $D=1+(d-1)\lambda$, $\Omega_\lambda(X)=\Delta_\lambda(X)+(1-\lambda)(X-\operatorname{diag}X)/d$, and $G=\operatorname{diag}(e^{2\pi i k/d})_{k=1}^d$. Then for every complex $d\times d$ matrix $X$,
--
--   $$\Delta_\lambda(X)=\frac{\lambda d}{D}\Omega_\lambda(X)+\frac{1-\lambda}{Dd}\sum_{k=1}^d(G^*)^k\Omega_\lambda(X)G^k.$$
--
--   Here $D\ge d/(d+1)>0$. This is an all-operator linear identity; its displayed coefficients can be signed and are not asserted to form a convex decomposition.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 13, Lemma 10: clock-unitary decomposition through the intermediate map

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

/-- King quant-ph/0204172v2, PDF p.13, Lemma 10, (49).
All-operator linear extensions; the default interval gives D>0.
This algebraic identity does not assert that its coefficients are nonnegative. -/
theorem clockIntermediateDecomposition {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    depolarizing d (1 - lam) X =
      (((lam * d / (1 + ((d : ℝ) - 1) * lam)) : ℝ) : ℂ) • intermediateChannel d lam X +
      ((((1 - lam) / ((1 + ((d : ℝ) - 1) * lam) * d)) : ℝ) : ℂ) •
        ∑ k : Fin d, conjSuperop ((clockUnitary d ^ (k.val + 1))ᴴ) (intermediateChannel d lam X) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
