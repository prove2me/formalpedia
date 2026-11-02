-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P74_degradable_key_rate
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P74.degradable_key_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:08:17.028436+00:00
-- url     : https://prove2.me/theorems/c4eb880b-516d-4ef1-a41b-b1bb3dd7ea9e
-- title:
--   Vanishing key rate under degradability to Eve
-- statement:
--   Let $\mathcal N:A'\to BE$ be a memoryless finite-register quantum wiretap channel with qubit input, with a fixed isometric extension $V:A'\to BES_2$. Choose two unit purifications $|\psi_z\rangle^{A'S_1}$ of the input states, with $z\in\{0,1\}$ equiprobable. Both shields $S_1,S_2$ are excluded from Eve. Let $W_{A,B}$ and $W_{A,E}$ be the resulting amplitude channels to Bob and Eve. The virtual phase channel $W_{P,B}$ has output $BCS_1S_2$, obtained by phase modulating the reference of the coherent source $2^{-1/2}\sum_z|z\rangle^C|\psi_z\rangle$ and tracing only Eve after $V$. Entropies and Holevo information are in bits, and $F$ denotes squared fidelity.
--
--   Fix $0<\beta<1/2$ and blocklength $N=2^n$. Use Arikan's fixed transform $G_N$ for amplitude and its transpose for phase; amplitude splitting reveals previous bits and averages future bits, while phase splitting reveals future bits and averages previous bits. An index is good precisely when its synthesized root fidelity is strictly less than $2^{-N^\beta}$. Write $\mathcal G_A,\mathcal G_P$ for the good sets and define $\mathcal A=\mathcal G_A\cap\mathcal G_P$, $\mathcal X=\mathcal G_A\setminus\mathcal G_P$, $\mathcal Z=\mathcal G_P\setminus\mathcal G_A$, and $\mathcal B=[N]\setminus(\mathcal G_A\cup\mathcal G_P)$. The code sends independent uniform private bits on $\mathcal A$, local random bits on $\mathcal X$, frozen bits known to Bob on $\mathcal Z$, and preshared uniform secret key bits on $\mathcal B$. Error and leakage average over these uniform choices.
--
--   Assume that a CPTP map $\mathcal D:B\to E$ satisfies $\mathcal D\circ\mathcal N_B=\mathcal N_E$ on all input operators. Then
--
--   $$
--   \lim_{n\to\infty}\frac{|\mathcal B_{2^n}|}{2^n}=0.
--   $$
--
--   This guarantees vanishing preshared-key consumption per channel use for this code. The degrading map targets Eve alone; it need not simulate the shield $S_2$.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, PDF p. 5, §III, unnumbered: vanishing key rate for degradable wiretap channels

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {B E S1 S2 : Type}

variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]

variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF p.5, §III: this scheme's key consumption RATE vanishes for channels degradable
to Eve's marginal; finite-block zero consumption is not claimed. -/
theorem degradable_key_rate (d : WiretapData B E S1 S2) (hd : d.Valid)
    (hdegradable : EveDegradable d) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1 / 2) :
    Filter.Tendsto (keyRate d beta) Filter.atTop (nhds 0) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P74
