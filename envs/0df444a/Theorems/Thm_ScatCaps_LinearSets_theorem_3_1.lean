-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_theorem_3_1
-- name    : ScatCaps.LinearSets.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:12.59018+00:00
-- url     : https://prove2.me/theorems/7863e202-6798-4dc8-ad6e-d5d6debbc67a
-- title:
--   Theorem 3.1, p. 16 — direct sums of scattered linear sets are scattered, of maximum rank iff each summand is
-- statement:
--   Let $\mathbb F_q\subseteq\mathbb F_{q^t}$ be finite fields, let $V$ be an $r$-dimensional $\mathbb F_{q^t}$-vector space, and let
--
--   $$
--   V=V_1\oplus_{\mathbb F_{q^t}}\cdots\oplus_{\mathbb F_{q^t}}V_m\tag{20}
--   $$
--
--   with $\dim V_i=s_i\ge2$, $m\ge1$. For each $i$ let $U_i\subseteq V_i$ be an $\mathbb F_q$-subspace such that $L_{U_i}$ is a scattered $\mathbb F_q$-linear set of $\mathrm{PG}(V_i,\mathbb F_{q^t})=\mathrm{PG}(s_i-1,q^t)$, and let
--
--   $$
--   W=U_1\oplus_{\mathbb F_q}\cdots\oplus_{\mathbb F_q}U_m.\tag{21}
--   $$
--
--   Then:
--
--   1. $L_W$ is a scattered $\mathbb F_q$-linear set of $\mathrm{PG}(V,\mathbb F_{q^t})=\mathrm{PG}(r-1,q^t)$;
--   2. for $t\ge2$, $L_W$ has rank $rt/2$ if and only if each $L_{U_i}$ has rank $s_it/2$.
--
--   This assembles the line and plane constructions into scattered linear sets of maximum rank in every $\mathrm{PG}(r-1,q^t)$.
--
--   **Formalization Note** The direct sum (20) is `DirectSum.IsInternal` for $K$-submodules $V_i$, and $W$ is the set of sums $u_1+\dots+u_m$. "Rank $rt/2$" is encoded as $|W|^2=q^{rt}$, i.e. $\dim_{\mathbb F_q}W=rt/2$, which needs no parity assumption on $rt$; likewise for $s_it/2$. Clause 2 carries $t\ge2$: the paper's proof uses the bound of Theorem 1.1 (rank $\le s_it/2$), which fails for $t=1$ (then $\mathbb F_q=\mathbb F_{q^t}$, every subspace is scattered, and e.g. $s=(3,3)$ with ranks $(2,1)$ is a counterexample). The paper works with proper extensions throughout; this hypothesis is a disclosed addition.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 16, Theorem 3.1, equations (20)–(21); proof p. 17

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem theorem_3_1 (K V : Type*) [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Fq : Subfield K) (q t r m : ℕ)
    (hq : Nat.card Fq = q) (hK : Fintype.card K = q ^ t)
    (hr : Module.finrank K V = r) (hm : 0 < m)
    (Vi : Fin m → Submodule K V) (hV : DirectSum.IsInternal Vi)
    (s : Fin m → ℕ)
    (hs : ∀ i, Module.finrank K (Vi i) = s i ∧ 2 ≤ s i)
    (Ui : Fin m → Set V)
    (hUi : ∀ i, Ui i ⊆ (Vi i : Set V) ∧
      IsFqSubspace Fq (Ui i) ∧ IsScattered Fq (⊤ : Subfield K) (Ui i)) :
    (IsFqSubspace Fq (directSumSet m Ui) ∧
      IsScattered Fq (⊤ : Subfield K) (directSumSet m Ui)) ∧
    (2 ≤ t →
      ((Nat.card (directSumSet m Ui)) ^ 2 = q ^ (r * t) ↔
        ∀ i, (Nat.card (Ui i)) ^ 2 = q ^ (s i * t))) := by sorry

end ScatCaps.LinearSets
