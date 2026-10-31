-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_cow_zero_overlap
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.cow_zero_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:39:58.117168+00:00
-- url     : https://prove2.me/theorems/2f83c879-f01b-4bc1-9218-e23fcb728073
-- title:
--   Feasible zero-overlap COW attacks outside the positive regime
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   Let $\mu>0$ and $\gamma=e^{-\mu}$. If $\gamma\le2\sqrt{V(1-V)}$ or $V\le1/2$, the explicitly constructed branchwise ancilla family, together with fresh orthogonal error flags, satisfies all COW Gram and monitoring constraints and has
--
--   $$\langle p_{0\mu}^{01},p_{\mu0}^{10}\rangle=0,\qquad \chi_{AE}=\chi_{BE}=1,\qquad r_0=-\frac\mu2h(Q)\le0.$$
--
--   Thus $V>1/2$ and $\gamma>2\sqrt{V(1-V)}$ are necessary for a positive rate in this attack analysis; they are not sufficient for security. The witness treats $V=0,1/2$ without singular angles. This preserves the source’s existence result while correcting its illustrative cosine choice.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 13, Appendix B, unnumbered: zero-overlap attack and necessary COW secrecy conditions

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

/-- Appendix B p.13: zero correct-state overlap outside the strict positive
regime, with full bit information and nonpositive signed DW coefficient. This is
an existence result inside the normalized ancilla model, not a finite-loss attack
realization or a claim about arbitrary postprocessed secret-key capacity.
Source correction: the printed illustrative cosine is replaced by cowZero's
solution of the overlap equation, avoiding both infeasible and singular angles.

Source correction audited in round 1.
Printed: PDF p.13: lambda=1, theta1=phi0=phi1=0, cos(theta0)=gamma*V/((1-V)*gamma+2*sqrt(V*(1-V))*sqrt(1-gamma^2)) is offered as a zero-overlap choice.
Changed: For V>1/2 in the zero regime, cowZero uses c=(V*gamma-A)/((1-V)*gamma+A), A=sqrt(V*(1-V))*sqrt(1-gamma^2); for V<=1/2 it uses independent residual directions with overlap -V*gamma/(1-V). All decoy constraints and the original zero-overlap existence conclusion are retained.
Why: B6/B7 give overlap V*gamma-A-((1-V)*gamma+A)*c. At gamma=3/5,V=4/5 the printed c=12/19 gives -56/475, whereas c=4/11 gives zero. The low-V branch also avoids infeasible or singular angles. Only an illustrative witness changes, not the claimed existence or its regime.
-/
theorem cow_zero_overlap (mu V : ℝ) (hmu : 0 < mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1)
    (hregime : Real.exp (-mu) ≤ 2*Real.sqrt (V*(1-V)) ∨ V ≤ 1/2) :
    CowValid (flaggedPair (cowZero mu V)) mu V false ∧
    inner ℂ ((cowZero mu V).p (false,true) true)
      ((cowZero mu V).p (true,false) false) = 0 ∧
    (∀ Q ∈ Set.Icc (0:ℝ) 1,
      binaryHolevoBits (cowA (flaggedPair (cowZero mu V)) Q false)
        (cowA (flaggedPair (cowZero mu V)) Q true) = 1 ∧
      binaryHolevoBits (cowB (flaggedPair (cowZero mu V)) Q false)
        (cowB (flaggedPair (cowZero mu V)) Q true) = 1 ∧
      cowCoefficient (cowZero mu V) mu Q = -mu/2*QAlgorithms.binEntropy2 Q ∧
      cowCoefficient (cowZero mu V) mu Q ≤ 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
