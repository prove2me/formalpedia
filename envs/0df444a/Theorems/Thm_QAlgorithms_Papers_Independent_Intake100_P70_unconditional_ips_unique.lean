-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_unconditional_ips_unique
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.unconditional_ips_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:52:32.416887+00:00
-- url     : https://prove2.me/theorems/17a7645e-c3cf-4c6b-9ee7-a6aa9f5054c1
-- title:
--   Unnumbered: universal recovery and unique unconditional IPS
-- statement:
--   Let $\mathcal E$ be a CPTP map between finite-dimensional nonzero complex Hilbert spaces,. Let $\widehat{\mathcal E}$ be the full-input transpose formula, completed on $\ker\mathcal E(I)$ by a maximally mixed replacement. This is CPTP, agrees with the raw formula on every $\mathcal E(X)$, and its composite $T=\widehat{\mathcal E}\circ\mathcal E$ determines the common unconditional structure
--
--   $$A=\operatorname{Fix}(T).$$
--
--   $A$ is a unital matrix star algebra. Every unconditionally preserved convex density code becomes noiseless under $T$ and embeds 1-isometrically into $A_+$; every maximum such code is isometric onto $A_+$. For every projective partition $\{P_k\}$, unconditional preservation is equivalent to $T(P_k)=P_k$ for all $k$. Unconditional simulation tests every physical density input. The distinguished formula need not be the only recovery map.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 15, Unnumbered: universal recovery and unique unconditional IPS

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF pp.15–17: the common full-input transpose recovery and its unique
unconditional algebraic structure. 'Unique recovery' means the distinguished
formula, not that no other CPTP extension or recovery can work. -/
theorem unconditional_ips_unique {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) :
    IsChannel (fullTransposeRecovery E) ∧
    (∀ rho, fullTransposeRecovery E (E rho) = transposeRecovery E 1 (E rho)) ∧
    UnconditionalStructure E (fixedOperators (fullTransposeRecovery E ∘ E)) ∧
    (∀ C, IsCode C → UnconditionalCode E C →
      Noiseless (fullTransposeRecovery E ∘ E) C) ∧
    (∀ m : ℕ, ∀ P : Fin m → Op I, ProjectiveMeasurement P →
      (UnconditionalMeasurement E P ↔
        ∀ k, fullTransposeRecovery E (E (P k)) = P k)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
