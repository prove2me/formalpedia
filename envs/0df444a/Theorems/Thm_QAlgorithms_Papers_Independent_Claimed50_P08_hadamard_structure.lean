-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P08_hadamard_structure
-- name    : QAlgorithms.Papers.Independent.Claimed50.P08.hadamard_structure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:14:19.926055+00:00
-- url     : https://prove2.me/theorems/d2eb5fc4-b364-409b-b536-34fd7edd7a4d
-- title:
--   Hadamard channel: explicit isometry, recovery and classical degradation
-- statement:
--   Let $A,B,C$ be nonzero finite-dimensional complex registers in fixed bases. Let $\{\lvert\phi_x\rangle\}_{x\in B}$ satisfy $\sum_x\lvert\phi_x\rangle\langle\phi_x\rvert=I_A$, and let every $\lvert\psi_x\rangle\in C$ be a unit vector. The $\phi_x$ need not be unit vectors. Define $U\lvert v\rangle=\sum_x\langle\phi_x\mid v\rangle\lvert x\rangle_B\lvert\psi_x\rangle_C$ and $\mathcal N(\sigma)=U\sigma U^\dagger$. Then $U^\dagger U=I_A$, $\mathcal N$ is CPTP, and for every operator $\sigma$ its matrix entries are $\mathcal N(\sigma)_{(x,c),(y,d)}=\langle\phi_x\mid\sigma\mid\phi_y\rangle\psi_x(c)\overline{\psi_y(d)}$. Its marginals are
--
--   $$
--   \mathcal N_B(\sigma)_{xy}=\langle\phi_x\mid\sigma\mid\phi_y\rangle\langle\psi_y\mid\psi_x\rangle,\qquad
--   \mathcal N_C(\sigma)=\sum_x\langle\phi_x\mid\sigma\mid\phi_x\rangle\lvert\psi_x\rangle\langle\psi_x\rvert.
--   $$
--
--   The explicit recovery channel $\operatorname{Rec}(\tau)=U^\dagger\tau U+(\operatorname{Tr}\tau-\operatorname{Tr}(U^\dagger\tau U))\lvert0\rangle\langle0\rvert$ is CPTP and satisfies $\operatorname{Rec}\circ\mathcal N=\operatorname{id}_A$. Identify $C'$ with $C$. The map $V\lvert x\rangle=\lvert x\rangle_B\lvert x\rangle_Y\lvert\psi_x\rangle_{C'}$ is an isometry, the basis measurement $\mathcal M$ and preparation $\mathcal P$ are CPTP, and the explicit degrading channel satisfies
--
--   $$
--   \mathcal D=\operatorname{Tr}_{BY}\circ(\tau\mapsto V\tau V^\dagger)=\mathcal P\circ\mathcal M,\qquad
--   \mathcal D\circ\mathcal N_B=\mathcal N_C.
--   $$
--
--   These are equalities on all operators. They explain why the stronger receiver can simulate the weaker receiver through a classical register.
--
--   **Formalization Note** Registers have dimension parameter plus one. The measurement input is $B$, correcting the printed $Y$ subscript below (7).
-- source:
--   Hadamard quantum broadcast channels, arXiv:1611.07651v3, PDF p. 2, §2, unnumbered: isometric Hadamard channel and classical degrading realization

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P08

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (groupedChannelPower mapFirst)

/-- PDF pp.2–3, Section 2, (1)–(8): the Hadamard broadcast map is isometric
and reversible, both marginals have the displayed formulas, and Charlie is
simulated by Bob's explicit isometry or by basis measurement and hadamardPreparation.
The measurement input subscript below (7) is corrected from Y to B. -/
theorem hadamard_structure {a b c : ℕ} (H : HadamardData a b c) :
    (inputIsometry H)ᴴ * inputIsometry H = 1 ∧
    IsChannel (hadamardChannel H) ∧
    (∀ (sigma : Op (BroadcastRegister a)) (p q : BroadcastRegister b × BroadcastRegister c),
      hadamardChannel H sigma p q =
        inputCoefficient H sigma p.1 q.1 * H.psi p.1 p.2 * conj (H.psi q.1 q.2)) ∧
    IsChannel (isometricRecovery H) ∧ isometricRecovery H ∘ hadamardChannel H = id ∧
    (∀ (sigma : Op (BroadcastRegister a)) (x y : BroadcastRegister b),
      bobChannel H sigma x y = inputCoefficient H sigma x y * inner ℂ (H.psi y) (H.psi x)) ∧
    (∀ sigma : Op (BroadcastRegister a), charlieChannel H sigma =
      ∑ x, inputCoefficient H sigma x x • pureDensity (H.psi x)) ∧
    (degradingIsometry H)ᴴ * degradingIsometry H = 1 ∧
    IsChannel (basisMeasurement (b := b)) ∧ IsChannel (hadamardPreparation H) ∧
    IsChannel (degradingChannel H) ∧
    degradingChannel H = hadamardPreparation H ∘ basisMeasurement ∧
    degradingChannel H ∘ bobChannel H = charlieChannel H := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P08

end
