-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_theorem_2_5
-- name    : ScatCaps.LinearSets.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:56.573977+00:00
-- url     : https://prove2.me/theorems/0a64af93-0262-4894-b00b-3cc346ac38ed
-- title:
--   Theorem 2.5, p. 10 — scattered 𝔽_q-linear sets of rank 3n exist in PG(2, q^{2n}) if n ≢ 0 mod 3, or if q ≡ 1 mod 3
-- statement:
--   Throughout, $q=p^h$ is a prime power, $n\ge2$, and $E=\mathbb F_{q^{6n}}$. For $m\in\{1,n,2n,3n\}$, $\mathbb F_{q^m}$ denotes the unique subfield of $E$ of order $q^m$, and $\mathbb F_{q^m}^*=\mathbb F_{q^m}\setminus\{0\}$. The field $E$ is a $3$-dimensional vector space over $\mathbb F_{q^{2n}}$, and $\mathbb P=\mathrm{PG}(\mathbb F_{q^{6n}},\mathbb F_{q^{2n}})=\mathrm{PG}(2,q^{2n})$ is the associated projective plane: its points are the $\mathbb F_{q^{2n}}$-spans $\langle v\rangle_{\mathbb F_{q^{2n}}}$ of nonzero $v\in E$.
--
--   Then:
--
--   1. if $n\not\equiv0\pmod3$, there is a scattered $\mathbb F_q$-linear set of rank $3n$ in $\mathrm{PG}(2,q^{2n})$, for every prime power $q$;
--   2. if $n\equiv0\pmod3$, there is a scattered $\mathbb F_q$-linear set of rank $3n$ in $\mathrm{PG}(2,q^{2n})$, for every prime power $q\equiv1\pmod3$.
--
--   In terms of subspaces: under either case hypothesis there is an $\mathbb F_q$-subspace $U\subseteq E$ with
--
--   $$
--   |U|=q^{3n}\quad\text{and}\quad L_U=\{\langle u\rangle_{\mathbb F_{q^{2n}}}:u\in U\setminus\{0\}\}\ \text{scattered}.
--   $$
--
--   This is the plane case $r=3$, $t=2n$ of Theorem 1.2.
--
--   **Formalization Note** $E$ is a finite field of characteristic $p$ with $|E|=q^{6n}$, and $\mathbb F_{q^m}$ is the fixed field of $x\mapsto x^{q^m}$. The linear set $L_U$ is represented by the $\mathbb F_q$-subspace $U$; "rank $3n$" is $|U|=q^{3n}$, and "scattered" is the weight-one condition in the form $u\in U\setminus\{0\},\ \lambda\in\mathbb F_{q^{2n}},\ \lambda u\in U\Rightarrow\lambda\in\mathbb F_q$, with points spanned over $\mathbb F_{q^{2n}}$ (not over $E$). The plane is represented by $E$ itself as a $3$-dimensional $\mathbb F_{q^{2n}}$-space, exactly as on p. 4. Rank $3n$ is part of the conclusion, so the zero subspace is not a witness.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 10, Theorem 2.5

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem theorem_2_5 (E : Type*) [Field E] [Fintype E]
    (p h q n : ℕ) [ExpChar E p] (hs : Section2Setting E p h q n)
    (hcase : n % 3 ≠ 0 ∨ (n % 3 = 0 ∧ q % 3 = 1)) :
    ∃ U : Set E, IsFqSubspace (subfieldOf E p h 1) U ∧
      HasRank (subfieldOf E p h 1) U (3 * n) ∧
      IsScattered (subfieldOf E p h 1) (subfieldOf E p h (2 * n)) U := by sorry

end ScatCaps.LinearSets
