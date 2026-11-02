-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P74_reliability
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P74.reliability
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:06:36.980456+00:00
-- url     : https://prove2.me/theorems/76d69315-d96f-42b4-8259-d51c5ec3ea0d
-- title:
--   Successive cancellation reliability, including the finite bound
-- statement:
--   Let $\mathcal N:A'\to BE$ be a memoryless finite-register quantum wiretap channel with qubit input, with a fixed isometric extension $V:A'\to BES_2$. Choose two unit purifications $|\psi_z\rangle^{A'S_1}$ of the input states, with $z\in\{0,1\}$ equiprobable. Both shields $S_1,S_2$ are excluded from Eve. Let $W_{A,B}$ and $W_{A,E}$ be the resulting amplitude channels to Bob and Eve. The virtual phase channel $W_{P,B}$ has output $BCS_1S_2$, obtained by phase modulating the reference of the coherent source $2^{-1/2}\sum_z|z\rangle^C|\psi_z\rangle$ and tracing only Eve after $V$. Entropies and Holevo information are in bits, and $F$ denotes squared fidelity.
--
--   Fix $0<\beta<1/2$ and blocklength $N=2^n$. Use Arikan's fixed transform $G_N$ for amplitude and its transpose for phase; amplitude splitting reveals previous bits and averages future bits, while phase splitting reveals future bits and averages previous bits. An index is good precisely when its synthesized root fidelity is strictly less than $2^{-N^\beta}$. Write $\mathcal G_A,\mathcal G_P$ for the good sets and define $\mathcal A=\mathcal G_A\cap\mathcal G_P$, $\mathcal X=\mathcal G_A\setminus\mathcal G_P$, $\mathcal Z=\mathcal G_P\setminus\mathcal G_A$, and $\mathcal B=[N]\setminus(\mathcal G_A\cup\mathcal G_P)$. The code sends independent uniform private bits on $\mathcal A$, local random bits on $\mathcal X$, frozen bits known to Bob on $\mathcal Z$, and preshared uniform secret key bits on $\mathcal B$. Error and leakage average over these uniform choices.
--
--   Let $\mathcal C=\mathcal A\cup\mathcal X$. There is a family of quantum successive cancellation POVMs on $B^N$, indexed by the known frozen and key bits and chosen independently of the unknown input bits, that decodes every bit in $\mathcal C$. Its average block error obeys
--
--   $$
--   \Pr\{\widehat U_{\mathcal C}\ne U_{\mathcal C}\}
--   \le b_n:=\sqrt{2\sum_{i\in\mathcal C}\sqrt{F(W_{A,B,N}^{(i)})}},
--   \qquad b_n=o\!\left(2^{-N^\beta/2}\right).
--   $$
--
--   The sequential decoder uses a binary projective test at each decoded index, adapting to the previous decisions; frozen indices require no test. This is a reliability statement for both information and locally randomized bits.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, PDF p. 4, §II.D, unnumbered: quantum successive cancellation reliability

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {B E S1 S2 : Type}

variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]

variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF p.4, §II.D: one input-independent POVM family recovers A union X using the
frozen/key bits. Both the finite bound and the printed little-o claim are retained.
The elementary cutoff estimate alone does not prove the latter; it is not assumed. -/
theorem reliability (d : WiretapData B E S1 S2) (hd : d.Valid)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1 / 2) :
    ∃ M : (n : ℕ) → PolarDecoderEffects d beta n,
      (∀ n, IsSuccessiveCancellation d beta n (M n)) ∧
      (∀ n k, IsPOVM (M n k)) ∧
      (∀ n, decoderError d beta n (M n) ≤ reliabilityBound d beta n) ∧
      Asymptotics.IsLittleO Filter.atTop (reliabilityBound d beta) (decayHalf beta) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P74
