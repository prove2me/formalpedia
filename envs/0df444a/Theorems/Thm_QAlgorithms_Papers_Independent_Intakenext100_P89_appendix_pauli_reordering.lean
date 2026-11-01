-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P89_appendix_pauli_reordering
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P89.appendix_pauli_reordering
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:31:00.438517+00:00
-- url     : https://prove2.me/theorems/fdb52287-1ebd-44c2-a56b-b60792952a70
-- title:
--   Pauli measurements: conditional-Z and Hadamard reordering instruments
-- statement:
--   Let $R$ be any finite nonempty unmeasured register, including arbitrary spectators, and let all input density operators be positive with trace one. Let $\{M_o\}_{o\in O}$ be any earlier measurement of qubit $a$, with a finite nonempty outcome set and $\sum_oM_o^\dagger M_o=I$. Its outcome $o$ controls $Z^{i(o)}$ on a distinct qubit $b$. A later unitary $U_{o,r}$ on $R$ is controlled by $o$ and by the Pauli outcome $r\in\{0,1\}$ on $b$; outcome zero means eigenvalue $+1$. Write $\mathcal L_{o,r}^{A}$ for the subnormalized residual branch after this sequence, discarding $a,b$. Define $f_X(i)=f_Y(i)=i$ and $f_Z(i)=0$. Let $\mathcal E_{o,t}^{A}$ instead measure $b$ before the earlier measurement, omit $Z^{i(o)}$, and apply $U_{o,t\oplus f_A(i(o))}$. Then, for every joint input state,
--
--   $$\mathcal L_{o,r}^{A}=\mathcal E_{o,r\oplus f_A(i(o))}^{A}\qquad(A=X,Y,Z).$$
--
--   For the Hadamard identities, let $P_{A,r}=(I+(-1)^rA)/2$, set $h(X)=Z,h(Z)=X,h(Y)=Y$ and $g(X)=g(Z)=0,g(Y)=1$. If $\operatorname{Tr}_b$ discards the measured qubit, then for every density $\sigma$ on $bR$,
--
--   $$\operatorname{Tr}_b\!\left[(P_{A,r}H\otimes I)\sigma(P_{A,r}H\otimes I)^\dagger\right]=\operatorname{Tr}_b\!\left[(P_{h(A),r\oplus g(A)}\otimes I)\sigma(P_{h(A),r\oplus g(A)}\otimes I)\right].$$
--
--   These identities include removal of $Z$ before a $Z$ measurement and the sign reversal for a $Y$ measurement after $H$. They preserve the joint outcome laws and residual states through the branch traces, not the measured output vectors. They make no assertion about equal loss accrued under different physical measurement times.
-- source:
--   Rate-distance tradeoff and resource costs for all-optical quantum repeaters, arXiv:1603.01353v4, PDF p. 15, Appendix A, Fig.8(a)–(c): Pauli measurement and feedforward identities

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

namespace QAlgorithms.Papers.Independent.Intakenext100.P89

open scoped BigOperators ComplexConjugate

-- Accepted probability primitives: symbol true is success; choose n x is zero for x > n.

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)

open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

noncomputable section

/-- Appendix A p.15, Fig.8(a)--(c): all conditional-Z and Hadamard measurement identities,
including the corrected downstream control of U. Equality is of subnormalized residual
branches after disposing of measured photons, hence of joint outcome probabilities and
residual states, with arbitrary finite references. No equality of measured output vectors
or time-dependent lossy hardware channels is asserted. -/
theorem appendix_pauli_reordering {O R : Type*} [Fintype O] [Nonempty O]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (MA : O → Matrix Bool Bool ℂ)
    (hMA : ∑ o, (MA o).conjTranspose * MA o = 1)
    (feed : O → Bool) (U : O → Bool → Matrix.unitaryGroup R ℂ) :
    (∀ (rho : Matrix ((Bool × Bool) × R) ((Bool × Bool) × R) ℂ),
      QAlgorithms.IsDensityMatrix rho → ∀ (a : PauliBasis) (o : O) (r : Bool),
        latePauliBranch MA feed U a o r rho =
          earlyPauliBranch MA feed U a o (xor r (zOutcomeFlip a (feed o))) rho) ∧
    (∀ (rho : Matrix (Bool × R) (Bool × R) ℂ), QAlgorithms.IsDensityMatrix rho →
      ∀ (a : PauliBasis) (r : Bool),
        effectDiscard (QAlgorithms.hadamard.conjTranspose * pauliProjector a r *
          QAlgorithms.hadamard) rho =
        effectDiscard (pauliProjector (hadamardBasis a)
          (xor r (hadamardOutcomeFlip a))) rho) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P89
