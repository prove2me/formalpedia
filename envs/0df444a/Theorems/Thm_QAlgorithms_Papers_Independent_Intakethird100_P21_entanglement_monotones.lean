-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_entanglement_monotones
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.entanglement_monotones
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:54:37.886034+00:00
-- url     : https://prove2.me/theorems/ce1ed8d6-c205-4677-a2a4-c59f5da130ca
-- title:
--   Concurrence and tangle are faithful selective LOCC monotones
-- statement:
--   Across all positive finite local dimensions, let $C$ be the convex roof of normalized pure I-concurrence and let $\tau$ be the convex roof of pure tangle. For either $E\in\{C,\tau\}$ and every bipartite density operator $\rho$, $E(\rho)\ge0$. For every complete local Kraus instrument on either party, including rectangular instruments that change its dimension, let $p_i$ and $\rho_i$ be the outcome probabilities and normalized posterior states. Then
--
--   $$
--   \sum_i p_i E(\rho_i)\le E(\rho),
--   \qquad E(\rho)=0\ \Longleftrightarrow\ \rho\text{ is separable}.
--   $$
--
--   A zero-probability outcome contributes zero without evaluating a cost on a normalized zero state. Both measures are invariant under local unitary conjugation. The local selective inequalities, together with density convexity, iterate through finite adaptive LOCC, including local pure ancillas and disposal.
--
--   These properties make both roofs faithful entanglement monotones in the source's finite-dimensional setting.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 5, §2: concurrence and tangle are faithful entanglement monotones

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Section 2: nonnegative selective local-instrument monotonicity
on all finite positive local dimensions, and vanishing exactly on separable states.
Together with convexity below these inequalities iterate through adaptive LOCC. -/
theorem entanglement_monotones :
    Frontier30.P30.IsLOCCMonotone (fun _ _ rho => tangle rho) ∧
    Frontier30.P30.IsLOCCMonotone (fun _ _ rho => concurrence rho) ∧
    ∀ a b : ℕ, ∀ ha : 0 < a, ∀ hb : 0 < b,
      ∀ rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ, IsDensityMatrix rho →
        letI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
        letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
        (tangle rho = 0 ↔ Entanglement.IsSeparableDensity rho) ∧
        (concurrence rho = 0 ↔ Entanglement.IsSeparableDensity rho) ∧
        ∀ U : Matrix.unitaryGroup (Fin a) ℂ, ∀ V : Matrix.unitaryGroup (Fin b) ℂ,
          let L := Matrix.kronecker (U : Matrix (Fin a) (Fin a) ℂ)
            (V : Matrix (Fin b) (Fin b) ℂ)
          tangle (L * rho * Lᴴ) = tangle rho ∧
          concurrence (L * rho * Lᴴ) = concurrence rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
