-- Prove2me | Theorems.Thm_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime
-- name    : ValuationSubring.exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/7998dcd3-f816-5c6c-864d-b8eaf026c98a
-- title:
--   Witt vectors of 𝔽̄ₚ inside a completion at a place over p
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ satisfying `LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb Q}$ lies in the nonunits of $A$ (so $p$ belongs to $A$ but is not invertible there). Write $C_A$ for the completion `A.valuation.Completion` of $\overline{\mathbb Q}$ with respect to the valuation attached to $A$, with valuation $v =$ `Valued.v`. The assertion is that there exist a field $k$ (in `Type`) of characteristic $p$ which is a perfect ring for $p$ and algebraically closed, together with a ring homomorphism $\psi \colon W(k) \to C_A$ from the ring of $p$-typical Witt vectors of $k$, such that: every $x \in k$ satisfies $x^{p^n} = x$ for some integer $n > 0$; $\psi$ is injective; $v(\psi(y)) \le 1$ for all $y \in W(k)$; and for every $z \in C_A$ with $v(z) \le 1$ there is $y \in W(k)$ with $v(z - \psi(y)) < 1$.
--
--   This is the classical fact that the residue field of the completion of $\overline{\mathbb Q}$ at a place above $p$ (a copy of $\mathbb C_p$) is an algebraic closure of $\mathbb F_p$, and that the Witt ring $W(\overline{\mathbb F}_p)$, the ring of integers of the completed maximal unramified extension of $\mathbb Q_p$, embeds integrally in $C_A$ so as to surject onto that residue field. It supplies the unramified part of the $p$-adic base data attached to a place of $\overline{\mathbb Q}$ used by [`CerednikDrinfeld.exists_adicBase_ratClosure`](thm.html#CerednikDrinfeld.exists_adicBase_ratClosure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k p) (_ : PerfectRing k p) (_ : IsAlgClosed k)
      (ψ : WittVector p k →+* A.valuation.Completion),
      (∀ x : k, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x) ∧
      Function.Injective ψ ∧
      (∀ y : WittVector p k, Valued.v (ψ y) ≤ 1) ∧
      (∀ z : A.valuation.Completion, Valued.v z ≤ 1 → ∃ y : WittVector p k, Valued.v (z - ψ y) < 1) := by sorry
