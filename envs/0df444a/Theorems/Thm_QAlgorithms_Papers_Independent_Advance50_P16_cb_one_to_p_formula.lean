-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_cb_one_to_p_formula
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.cb_one_to_p_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:35:43.542703+00:00
-- url     : https://prove2.me/theorems/4e2d3fd1-5030-491d-83f8-1ee3a857da8a
-- title:
--   Theorem 10: Choi and pure-input formulas for the CB 1-to-p norm
-- statement:
--   For any complex-linear CP map $\Phi:M_m\to M_n$ with $m,n\ge1$, and any $1\le p\le\infty$, let $X_\Phi=\sum_{ij}|i\rangle\langle j|\otimes\Phi(|i\rangle\langle j|)$ be the unnormalized Choi matrix. Then
--
--   $$\|\Phi\|_{\mathrm{CB},1\to p}=\|X_\Phi\|_{(\infty,p)}=\sup_{\|\psi\|=1}\frac{\|(\mathrm{id}_m\otimes\Phi)(|\psi\rangle\langle\psi|)\|_p}{\|\operatorname{Tr}_2(|\psi\rangle\langle\psi|)\|_p}=\omega_p(\Phi).$$
--
--   The unit vector ranges over $\mathbb C^m\otimes\mathbb C^m$. CB norm uses the same outer exponent on the input and output mixed norms and a supremum over every positive finite ancilla. No trace-preservation hypothesis is imposed. This identifies the channel quantity with a CB norm and a Choi mixed norm.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 18, Theorem 10: Choi and pure-input formulas for the CB 1-to-p norm

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

/-- Theorem 10 / (3.31), PDF p.18: CP suffices; the Choi matrix is unnormalized. -/
theorem cb_one_to_p_formula {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Phi : (Mat I →ₗ[ℂ] Mat J)) (hPhi : Entanglement.IsCompletelyPositive Phi) :
    cbSize 1 p Phi = ENNReal.ofReal (mixedNorm ⊤ p (choi Phi)) ∧
      mixedNorm ⊤ p (choi Phi) = cbOmega p Phi := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
