-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_erasureSeparation
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.erasureSeparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:39:41.432183+00:00
-- url     : https://prove2.me/theorems/0c961bac-a1d6-4e3c-849e-ad66a29898da
-- title:
--   Qubit erasure operational and signed-information separation
-- statement:
--   Operational capacities are supremal asymptotic ebits per physical channel use, with vanishing full-state trace-norm error, arbitrary finite block memories, and no initial shared entanglement. $E$ allows local processing without classical assistance; $E_{\leftarrow}$ permits adaptive feedback; $E_{\leftrightarrow}$ permits both classical directions. $E_{\triangleleft}$ sends the entire block before one final Bob-to-Alice message and Alice's conditional operation. Rate zero is included. Let $0<\epsilon<1$ be the erasure probability of the literal qubit erasure channel $\mathcal E_\epsilon(\rho)=(1-\epsilon)\rho\oplus\epsilon\operatorname{Tr}(\rho)|e\rangle\langle e|$, where the flag is orthogonal to the input space. Write $H_2$ for binary entropy in bits. Then
--
--   $$E_{\leftrightarrow}(\mathcal E_\epsilon)=E_{\triangleleft}(\mathcal E_\epsilon)=1-\epsilon,\quad
--   E(\mathcal E_\epsilon)=\max\{1-2\epsilon,0\},\quad
--   R_1(\mathcal E_\epsilon)=1-\epsilon-H_2(\epsilon),$$
--   $$E_{\leftrightarrow}=E_{\triangleleft}>E>R_1.$$
--
--   The formal statement constructs a physical dilation realizing the literal erasure map and its signed maximum. This separation distinguishes a restricted entropy yield from a reverse-protocol operational rate.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 3, erasure comparison paragraph

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

/-- PDF p.3: qubit erasure operational and signed entropy separation.
The printed strict comparisons require 0<erasure<1; at endpoints they collapse.
The literal orthogonal-flag erasure map is the pinned accepted erasureFin. -/
theorem erasureSeparation (erasure : ℝ) (h0 : 0 < erasure) (h1 : erasure < 1) :
    entanglementCapacity (erasureFin 2 erasure) .twoWay = reverseCapacity (erasureFin 2 erasure) ∧
    reverseCapacity (erasureFin 2 erasure) = ((1-erasure : ℝ) : EReal) ∧
    entanglementCapacity (erasureFin 2 erasure) .unassisted =
      ((max (1-2*erasure) 0 : ℝ) : EReal) ∧
    (∃ V : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ,
      IsIsometry V ∧ receiverChannel V = erasureFin 2 erasure ∧
      reverseMaximum V = 1-erasure-binEntropy2 erasure) ∧
    ((max (1-2*erasure) 0 : ℝ) : EReal) < reverseCapacity (erasureFin 2 erasure) ∧
    1-erasure-binEntropy2 erasure < max (1-2*erasure) 0 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
