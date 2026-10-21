-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_partialTrace_coherentInformation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.partialTrace_coherentInformation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:01:56.956909+00:00
-- url     : https://prove2.me/theorems/d80848d2-adf1-4853-93b8-3cd384783462
-- title:
--   Coherent information of the two partial-trace channels
-- statement:
--   Let rho_ABC be a pure normalized trace-class state on three separable complex systems, with H(C)<infinity. Write I(rho,Phi) for channel mutual information, I_c(rho,Phi)=I(rho,Phi)-H(rho) for finite-input coherent information, and D for quantum relative entropy, all in natural-log units. For the common input rho_AB,
--   $$\begin{aligned}
--   I_c(\rho_{AB},\operatorname{Tr}_B)&=I(\rho_{AB},\operatorname{Tr}_B)-H(AB)\\
--   &=D(\rho_{AC}\Vert\rho_A\otimes\rho_C)-H(C)=-H(C|A),\\
--   I_c(\rho_{AB},\operatorname{Tr}_A)&=I(\rho_{AB},\operatorname{Tr}_A)-H(AB)\\
--   &=D(\rho_{BC}\Vert\rho_B\otimes\rho_C)-H(C)=-H(C|B).
--   \end{aligned}$$
--
--   These identities relate the conditional entropies to complementary partial-trace channels. Purity ensures finite H(AB)=H(C); H(A) and H(B) need not be finite.
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1, identities (3)–(4): partial-trace coherent information equals negative conditional entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

/-- Both full chains of identities (3)–(4), PDF p.2. The state ABC is pure;
Tr_B retains A and Tr_A retains B. Only H(C) is assumed finite. -/
theorem partialTrace_coherentInformation {A B C : Type}
    [Countable A] [Countable B] [Countable C] (rho : PureState ((A × B) × C))
    (hC : homogeneousEntropy (traceFirst rho.val.coefficients) < ⊤) :
    let ab := traceSecond rho.val.coefficients
    let ac := dropMiddle (associateRight rho.val.coefficients)
    let bc := traceFirst (associateRight rho.val.coefficients)
    let c := traceFirst rho.val.coefficients
    let dAC := generalizedRelativeEntropy ac (productCoeff (traceSecond ac) c)
    let dBC := generalizedRelativeEntropy bc (productCoeff (traceSecond bc) c)
    ((finiteInputCoherentInfo ab (@traceSecond A B) : EReal) =
        (mutualInformation ab (@traceSecond A B) : EReal) - (homogeneousEntropy ab : EReal) ∧
      (mutualInformation ab (@traceSecond A B) : EReal) - (homogeneousEntropy ab : EReal) =
        (dAC : EReal) - (homogeneousEntropy c : EReal) ∧
      (dAC : EReal) - (homogeneousEntropy c : EReal) = -finiteFirstConditionalEntropy (swapCoeff ac)) ∧
    ((finiteInputCoherentInfo ab (@traceFirst A B) : EReal) =
        (mutualInformation ab (@traceFirst A B) : EReal) - (homogeneousEntropy ab : EReal) ∧
      (mutualInformation ab (@traceFirst A B) : EReal) - (homogeneousEntropy ab : EReal) =
        (dBC : EReal) - (homogeneousEntropy c : EReal) ∧
      (dBC : EReal) - (homogeneousEntropy c : EReal) = -finiteFirstConditionalEntropy (swapCoeff bc)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
