-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P64_fullyQuantumSlepianWolf
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P64.fullyQuantumSlepianWolf
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:36:50.76421+00:00
-- url     : https://prove2.me/theorems/8a29fdba-5881-4b27-b656-7bcd4e29e6f4
-- title:
--   Fully quantum Slepian-Wolf with joint source and Bell output
-- statement:
--   Let $R,S,A,B$ be finite nonzero registers, let $|\phi\rangle^{RS}$ be a unit vector supplied by a separate Source, and let $U:S\to A\otimes B$ be an isometry. Set $|\psi\rangle^{RAB}=(I_R\otimes U)|\phi\rangle$ and $\rho^S=\operatorname{Tr}_R|\phi\rangle\langle\phi|$. Alice receives $A$ and Bob receives $B$; neither controls the Source input. Entropies and mutual informations are in bits. Then
--
--   $$
--   \langle U^{S\to AB}:\rho^S\rangle+
--   \tfrac12 I(R;A)_\psi[q\to q]
--   \ge\tfrac12 I(A;B)_\psi[qq]+
--   \langle\mathrm{id}^{S\to\widehat B}:\rho^S\rangle.
--   $$
--
--   For every $\varepsilon,\delta>0$, all sufficiently large positive $n$ admit local isometric encoding and decoding dilations with retained local work. Alice sends a $q$-qubit register to Bob and keeps one half of each of $l$ generated Bell pairs. Bob receives the other halves and a copy $\widehat B^n$ of $S^n$, where
--
--   $$
--   q\le\lfloor n(I(R;A)_\psi/2+\delta)\rfloor,\qquad
--   l\ge\max\{0,\lfloor n(I(A;B)_\psi/2-\delta)\rfloor\}.
--   $$
--
--   After tracing local work, the complete output on $R^n,\widehat B^n$ and both Bell registers is within full trace norm $\varepsilon$ of $|\phi\rangle\langle\phi|^{\otimes n}\otimes\Phi^{\otimes l}$. The protocol uses no input Bell pairs or other nonlocal assistance and never acts on $R$.
--
--   This transfers the source and generates entanglement simultaneously. The paper attributes the FQSW inequality to [11]; the statement does not claim that arbitrary discarded-work protocols can be reversed.
-- source:
--   A triangle of dualities: reversibly decomposable quantum channels, source-channel duality, and time reversal, arXiv:quant-ph/0505138v1, PDF p. 3, Equation (12) and Figure 4: fully quantum Slepian-Wolf

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P64

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P64

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P20
  (Copies redistributionMarginal subsystemEntropy forwardApply)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, (12), and p.4, Fig.4; attributed there to [11]: fully quantum
Slepian-Wolf. Source-controlled phi is distributed only by U. The fixed code
transfers the original S to Bob and produces independent Bell pairs, jointly
with untouched R, at the displayed two rates. Isometric dilations retain work. -/
theorem fullyQuantumSlepianWolf {R S A B : Type}
    [Fintype R] [Fintype S] [Fintype A] [Fintype B]
    [Nonempty R] [Nonempty S] [Nonempty A] [Nonempty B]
    (U : Matrix (A × B) S ℂ) (hU : Uᴴ * U = 1)
    (phi : EuclideanSpace ℂ (R × S)) (hphi : IsState phi) :
    SourceTransferAchievable U phi
      (mutualRA (feedbackOutputVector U phi) / 2) (mutualAB (feedbackOutputVector U phi) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P64

end
