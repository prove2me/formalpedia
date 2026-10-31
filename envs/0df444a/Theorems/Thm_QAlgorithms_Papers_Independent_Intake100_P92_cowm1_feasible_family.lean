-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_cowm1_feasible_family
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.cowm1_feasible_family
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:40:55.010746+00:00
-- url     : https://prove2.me/theorems/46212860-4850-4e18-b54f-d686786bc047
-- title:
--   Explicit feasible three-parameter COWm1 ancilla family
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   Let $\mu>0$, $\gamma=e^{-\mu}$, and let $\theta_0,\theta_1,\phi\in\mathbb R$ be arbitrary. Construct exactly the four-dimensional vacuum vectors (C2), perpendicular directions (C3),(C4), and photon vectors (C5)–(C10). Add the four independent unconstrained error flags in fresh coordinates. Every resulting vector is normalized, every vacuum overlap (B1),(C1) holds, and
--
--   $$\langle p_{\mu\mu}^{01},p_{\mu\mu}^{10}\rangle=V,\qquad \langle v_x,p_x^{\rm monitored}\rangle=\sqrt V$$
--
--   for both correct key vectors and both decoy photon vectors. Hence all five visibility constraints hold. The four-dimensional assertion concerns the displayed participating vectors; the error flags occupy extra dimensions. This supplies a feasible three-parameter family for the COWm1 information calculation, without asserting numerical or global optimality.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 14, Appendix C, (C2)–(C10): explicit three-parameter feasible COWm1 attack family

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P92

open QAlgorithms.Papers.Independent.Information100.P21 (Vec tensor)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (Fock coherentPair coherentPairCoefficients passiveApply passiveCoefficients
   fockReducedFirst reducedSecond coherentCoefficient)

/-- Appendix C pp.13–14, (C2)–(C10): every three-angle choice constructs a
feasible four-dimensional participating family, with its stronger visibility
identities. Feasibility does not assert numerical or global optimality.

Source correction audited in round 1.
Printed: PDF p.14, Appendix C parenthetical, lists p_mumu^10 and p_mumu^01 among the vectors already chosen orthogonal to all other states.
Changed: Replace those two labels by p_00^10 and p_00^01 in the error-flag list. Keep the displayed C2-C10 participating vectors unchanged; flaggedPair supplies the four independent error directions.
Why: Section IV B on p.6 and (17),(18) identify the vacuum-input photon vectors as free. The decoy photon vectors are constrained by (B2) and constructed in (C6),(C9),(C10); the printed parenthetical contradicts this construction.
-/
theorem cowm1_feasible_family (mu V theta0 theta1 phi : ℝ) (hmu : 0 < mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1) :
    CowValid (flaggedPair (cowm1Family mu V theta0 theta1 phi)) mu V true ∧
    (let A := cowm1Family mu V theta0 theta1 phi
     inner ℂ (A.p (true,true) true) (A.p (true,true) false) = (V : ℂ) ∧
     inner ℂ (A.v (false,true)) (A.p (false,true) true) = (Real.sqrt V : ℂ) ∧
     inner ℂ (A.v (true,false)) (A.p (true,false) false) = (Real.sqrt V : ℂ) ∧
     ∀ b, inner ℂ (A.v (true,true)) (A.p (true,true) b) = (Real.sqrt V : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
