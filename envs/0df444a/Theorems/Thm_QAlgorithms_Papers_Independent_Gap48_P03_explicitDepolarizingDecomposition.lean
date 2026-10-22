-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_explicitDepolarizingDecomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.explicitDepolarizingDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:02:14.346354+00:00
-- url     : https://prove2.me/theorems/ec587f4a-503c-45bf-ac23-1489b7f99e67
-- title:
--   The explicit constructed depolarizing decomposition
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. Define $D=1+(d-1)\lambda$, $G_{kk}=e^{2\pi i k/d}$, $H_{kk}=e^{2\pi i k^2/(2d^2)}$, and $\theta=d^{-1/2}(1,\ldots,1)$, with diagonal $G,H$ and one-based indices. Let $u_{k,a}=G^kH^a\theta$, $E_{k,a}=|u_{k,a}\rangle\langle u_{k,a}|$, and $\Phi_\lambda^{(a)}(X)=\lambda X+(1-\lambda)\sum_k E_{k,a}XE_{k,a}$. These constructed bases are uniform. For every state $\rho$,
--
--   $$\Delta_\lambda(\rho)=\frac{\lambda}{2dD}\sum_{a=1}^{2d^2}\Phi_\lambda^{(a)}(\rho)+\frac{1-\lambda}{2d^3D}\sum_{k=1}^d\sum_{a=1}^{2d^2}(G^*)^k\Phi_\lambda^{(a)}(\rho)G^k.$$
--
--   This retains the explicit family behind the existence decomposition. The ungrouped coefficients can be signed for negative $\lambda$; grouping the identity-conjugation terms gives its convex interpretation.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 16, Explicit unnumbered decomposition (71): the constructed family for Δλ

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

/-- King quant-ph/0204172v2, PDF p.16, (71): the exact constructed family.
The first coefficient is lambda/(D*2d). For negative lambda the ungrouped
weights are signed; group the G^d=I terms for the convex interpretation. -/
theorem explicitDepolarizingDecomposition {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1) :
    (∀ a : Fin (2 * d^2), IsUniformBasis (constructedUniformBasis d (a.val + 1))) ∧
    ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      depolarizing d (1 - lam) rho =
        (((lam / ((1 + ((d : ℝ) - 1) * lam) * (2 * d))) : ℝ) : ℂ) •
          (∑ a : Fin (2 * d^2), constructedPhaseDamping d lam (a.val + 1) rho) +
        ((((1 - lam) / ((1 + ((d : ℝ) - 1) * lam) * (2 * (d : ℝ)^3))) : ℝ) : ℂ) •
          ∑ k : Fin d, ∑ a : Fin (2 * d^2),
            conjSuperop ((clockUnitary d ^ (k.val + 1))ᴴ)
              (constructedPhaseDamping d lam (a.val + 1) rho) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
