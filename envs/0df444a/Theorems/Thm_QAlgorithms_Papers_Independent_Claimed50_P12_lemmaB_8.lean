-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_8
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_8
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:44:37.337678+00:00
-- url     : https://prove2.me/theorems/3b95da26-8db0-446e-a774-588f6fa593af
-- title:
--   One-sided local trace non-increasing fidelity bound
-- statement:
--   Let $D,E$ be nonzero finite-dimensional complex Hilbert spaces, let $\rho_{DE},\sigma_{DE}\ge0$, and let $W_E$ be CP and trace non-increasing on $E$. With $\rho_D=\operatorname{tr}_E\rho_{DE}$ and $\sigma_D=\operatorname{tr}_E\sigma_{DE}$,
--
--   $$F\bigl(\rho_{DE},(\mathrm{id}_D\otimes W_E)(\sigma_{DE})\bigr)\le F(\rho_D,\sigma_D).$$
--
--   Here $F$ is root fidelity; neither input needs normalization. The channel acts only on the second fidelity argument and retains entangled off-diagonal blocks. This gives the local filtering comparison used in Section 4.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 22, Lemma B.8

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma B.8, Eq.169 (PDF p.22): TNI channel on the SECOND argument only. -/
theorem lemmaB_8 {D E : Type*} [Fintype D] [Fintype E]
    [DecidableEq D] [DecidableEq E] [Nonempty D] [Nonempty E]
    (rho sigma : Op (D × E)) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (W : Superop E E) (hW : TNI W) :
    rootFidelity rho (idTensorSuperop W sigma) ≤
      rootFidelity (traceRight rho) (traceRight sigma) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
