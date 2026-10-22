-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_reverseInformation_main
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.reverseInformation_main
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:36:21.926222+00:00
-- url     : https://prove2.me/theorems/4f2e4e13-af97-4414-9f8b-9f334ea6b795
-- title:
--   Operational lower bound and single-letter reverse coherent information
-- statement:
--   All registers are finite. A physical channel is completely positive and trace preserving; its fixed Stinespring isometry $V:A\to B\otimes E$ defines the receiver channel $\Lambda$ and its complementary channel $\Lambda^c$. Inputs $\rho$ are positive semidefinite of trace one. Entropies are in bits. Write $I(\Lambda,\rho)=S(\Lambda(\rho))-S(\Lambda^c(\rho))$ and $I_R(\Lambda,\rho)=S(\rho)-S(\Lambda^c(\rho))$. These equal the purified-reference definitions, with the reference retained by Alice.
--
--   Operational capacities are supremal asymptotic ebits per physical channel use, with vanishing full-state trace-norm error, arbitrary finite block memories, and no initial shared entanglement. $E$ allows local processing without classical assistance; $E_{\leftarrow}$ permits adaptive feedback; $E_{\leftrightarrow}$ permits both classical directions. $E_{\triangleleft}$ sends the entire block before one final Bob-to-Alice message and Alice's conditional operation. Rate zero is included. For a nonzero input register, let $R_1(\Lambda)=\max_\rho I_R(\Lambda,\rho)$, retaining its sign. Then
--
--   $$
--   \max_{\rho_n}I_R(\Lambda^{\otimes n},\rho_n)=nR_1(\Lambda)\quad(n\ge1),\qquad
--   \frac1n\max_{\rho_n}I_R(\Lambda^{\otimes n},\rho_n)\longrightarrow R_1(\Lambda),
--   \qquad R_1(\Lambda)\le E_{\triangleleft}(\Lambda)\le E_{\leftarrow}(\Lambda).
--   $$
--
--   The block maximization includes correlated inputs. This supplies a single-letter first-order lower bound without identifying the signed entropy maximum with either operational capacity.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 3, pp.1–3, Eqs.(4)–(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3: optimized signed reverse information is single-letter, its normalized
block maxima converge to that value, and it lower-bounds the operational reverse
protocol capacity, which is at most the feedback-assisted capacity. -/
theorem reverseInformation_main {a b e : ℕ} (ha : 0 < a)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : IsIsometry V) :
    (∀ n : ℕ, 0 < n → reverseMaximum (dilationPower V n) = (n : ℝ)*reverseMaximum V) ∧
    Tendsto (fun n : ℕ => reverseMaximum (dilationPower V n)/(n : ℝ))
      atTop (nhds (reverseMaximum V)) ∧
    (reverseMaximum V : EReal) ≤ reverseCapacity (receiverChannel V) ∧
    reverseCapacity (receiverChannel V) ≤ entanglementCapacity (receiverChannel V) .feedback := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
