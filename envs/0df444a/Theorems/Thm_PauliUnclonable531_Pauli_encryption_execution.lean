-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_encryption_execution
-- name    : PauliUnclonable531.Pauli.encryption_execution
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-10T09:01:44.727381+00:00
-- url     : https://prove2.me/theorems/31ffc272-fcec-4783-9672-41112369fae6
-- title:
--   §3.1 — the encryption instructions realize the parity ensemble
-- statement:
--   Fix $n\ge 1$, a nonidentity Pauli key $k=(x,z)\in\mathbb F_2^n\times\mathbb F_2^n$ and a message bit $m$. The §3.1 encryption procedure first scans the key for its pivot $p$ (the least position with $(x_p,z_p)\neq(0,0)$), then draws a fair bit $r_j$ for every position $j\neq p$, sets $r_p = m\oplus\bigoplus_{j\neq p,\ (x_j,z_j)\ne(0,0)} r_j$, prepares $|r\rangle$ from $|0^n\rangle$ by applying $X$ on the wires with $r_j=1$, and finally applies $H$ on every wire with $x_j=1$, followed by $S$ when also $z_j=1$.
--
--   Let $\mathcal E_{k,m}$ be the state output by this procedure averaged over the $2^{n-1}$ equally likely random tapes (all actual gate matrices $X,H,S$ are used, each acting on its wire of the possibly entangled $n$-qubit register). Then
--
--   $$\mathcal E_{k,m}=2^{-(n-1)}\sum_{r\in\mathbb F_2^n:\ \bigoplus_j q_j r_j=m}U_k|r\rangle\langle r|U_k^\dagger ,$$
--
--   where $q_j=1$ exactly at the nonidentity positions of $k$ and $U_k=\bigotimes_j V_j$ with $V_j=I$ if $x_j=0$, $V_j=H$ if $(x_j,z_j)=(1,0)$, $V_j=SH$ if $(x_j,z_j)=(1,1)$.
--
--   Together with Proposition 3.2 (the right-hand side equals the ciphertext $\rho_{k,m}=2^{-n}(I+(-1)^mP_k)$), this shows that the explicit instruction list of §3.1 prepares exactly the ciphertext of the scheme.
--
--   **Formalization Note.** The procedure is the instruction list `encProgram k`, executed by `executeEnc` on a tape `Tape k` (bit strings vanishing at the pivot); `operationalEnc` averages over all tapes with uniform weight.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits and real Born probabilities; reason: these are the same finite-dimensional objects after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026) / arXiv:2607.21551v4, §3.1, pp.16–17 (efficient encryption procedure) together with Proposition 3.2, Eq. (15), p.16

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Ensemble

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

theorem encryption_execution (n : ℕ) (hn : 1 ≤ n) (k : Key n) (m : Fin 2) :
    operationalEnc k m = parityEnsemble k m := by sorry

end PauliUnclonable531.Pauli
