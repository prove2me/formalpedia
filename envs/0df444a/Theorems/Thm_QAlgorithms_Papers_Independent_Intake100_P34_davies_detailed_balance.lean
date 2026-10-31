-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_davies_detailed_balance
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.davies_detailed_balance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:22:39.817771+00:00
-- url     : https://prove2.me/theorems/4da4e13b-929f-4b53-99c7-208fced390af
-- title:
--   §4 — finite Davies-generator detailed balance
-- statement:
--   Let $d>0$, $H=H^*$, and let the finite self-adjoint couplings be $Q_j^{(k)}$, with positive inverse temperatures $\beta_j$. For every Bohr difference $\omega$, assume $h_j(\omega)\ge0$, $h_j^{kl}(-\omega)=e^{-\beta_j\omega}h_j^{lk}(\omega)$, and $s_j(\omega)=s_j(\omega)^*$. Construct $V_j^{(k)}(\omega)=\sum_{\mu-\nu=\omega}P_\nu Q_j^{(k)}P_\mu$ from the spectral projections of $H$, and set $T_j=\sum_{k,l,\omega}s_j^{kl}(\omega)V_j^{(k)}(\omega)^*V_j^{(l)}(\omega)$ and $\Phi_j(X)=\sum_{k,l,\omega}h_j^{kl}(\omega)V_j^{(k)}(\omega)^*XV_j^{(l)}(\omega)$. Then
--
--   $$L_j=i[T_j,\cdot]-\tfrac12\{\Phi_j(1),\cdot\}+\Phi_j$$
--
--   satisfies detailed balance for $\rho_j=e^{-\beta_jH}/\operatorname{tr}(e^{-\beta_jH})$. In particular $T_j$ is self-adjoint, $\Phi_j$ is CP and $\rho_j$-self-adjoint, each $L_j$ generates a QDS and fixes $\rho_j$, and their sum generates a QDS. This is the finite algebraic Davies construction; no microscopic limit identification is assumed.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 16, §4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF pp.15–16, (30)–(33): finite spectral Davies generators satisfy DB and KMS.
No conclusion identifies them with an arbitrary alleged microscopic weak-coupling limit. -/
theorem davies_detailed_balance {d M : ℕ} (D : DaviesData d M) :
    (∀ j, (daviesT D j).IsHermitian ∧
      QAlgorithms.Entanglement.IsCompletelyPositive (daviesPhi D j) ∧
      weightedAdjoint (qdsGibbsDensity D.H (D.beta j)) (daviesPhi D j) = daviesPhi D j ∧
      DetailedBalance (qdsGibbsDensity D.H (D.beta j)) (daviesGenerator D j)) ∧
    IsQDS (∑ j, daviesGenerator D j) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
