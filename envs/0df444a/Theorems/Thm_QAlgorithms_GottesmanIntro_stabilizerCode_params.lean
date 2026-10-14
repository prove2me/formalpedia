-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_stabilizerCode_params
-- name    : QAlgorithms.GottesmanIntro.stabilizerCode_params
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:58:02.546785+00:00
-- url     : https://prove2.me/theorems/b7e6e349-3d5d-49b5-bd85-c8caf73e61af
-- title:
--   Stabilizer codes: an Abelian S of order 2^a without -1 gives an [[n, n-a, d]] code
-- statement:
--   Let $\mathcal P_n$ be the $n$-qubit Pauli group: the operators $i^c\,\sigma_1\otimes\cdots\otimes\sigma_n$ with $c\in\{0,1,2,3\}$ and $\sigma_j\in\{I,X,Y,Z\}$. The weight $\mathrm{wt}(Q)$ of a Pauli operator is the number of its tensor factors different from $I$.
--
--   Let $S\le\mathcal P_n$ be an Abelian subgroup of order $|S|=2^a$ with $-I\notin S$, and let
--   $$T(S)=\{\,|\psi\rangle : M|\psi\rangle=|\psi\rangle\ \text{for all } M\in S\,\}$$
--   be its stabilized space. Let $N(S)$ be the set of Pauli operators commuting with every element of $S$ (the normalizer of $S$ in $\mathcal P_n$, which equals its centralizer), and suppose
--   $$d=\min\{\mathrm{wt}(Q) : Q\in N(S),\ Q\notin\{i^cM : M\in S,\ c\in\{0,1,2,3\}\}\}$$
--   exists (the set is nonempty). Then $T(S)$ is an $[[n,n-a,d]]$ quantum code:
--
--   1. $\dim T(S)=2^{n-a}$;
--   2. every operator $E$ acting on at most $d-1$ qubits is detectable, i.e. $\langle\psi|E|\psi\rangle$ takes the same value $C(E)$ for every normalized $|\psi\rangle\in T(S)$;
--   3. some operator acting on at most $d$ qubits is not detectable, so the distance is exactly $d$.
--
--   This is the basic theorem of the stabilizer formalism: it reads the parameters of a quantum code off a group of commuting Pauli operators.
--
--   **Formalization Note** The source writes $N(S)\setminus S$; taken literally this set always contains $-I$ (weight $0$), so, following the standard convention the source cites, Pauli operators equal to a phase times an element of $S$ are removed. The minimum is encoded with `IsLeast`, which also excludes the case $a=n$ where the set is empty and the source's $d$ is undefined.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 10, Theorem 5. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_QECC
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro

open Stabilizer

/-- Gottesman intro p.10, Theorem 5: let `S` be an Abelian subgroup of order `2^a` of the
`n`-qubit Pauli group with `−1 ∉ S`, and let `d` be the minimum weight of a Pauli operator in
the normalizer `N(S)` (= the centralizer of `S` in `P_n`, p.10) that is not a phase times an
element of `S`. Then the stabilized space `T(S)` is an `[[n, n − a, d]]` code: it has dimension
`2^(n−a)`, every operator acting on at most `d − 1` qubits satisfies (34) on it, and some
operator acting on `d` qubits does not. The weight of a Pauli operator is the number of
non-identity tensor factors (p.4). The phases `±1, ±i` are removed from `N(S) \ S` since
otherwise `−I` (weight 0) would always lie in it. -/
theorem stabilizerCode_params (n a d : ℕ) (S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (hS : IsStabilizerGroup S) (hcard : Nat.card S = 2 ^ a)
    (hd : IsLeast {w : ℕ | ∃ Q ∈ pauliCentralizer S, Q ∉ phaseMultiples S ∧
      ∃ P : PauliString n, (Q : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix ∧ P.weight = w} d) :
    IsQCode n (n - a) d (stabilizedSpace S) ∧ HasDistance (stabilizedSpace S) d := by
  sorry


end QAlgorithms.GottesmanIntro
