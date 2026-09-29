-- Prove2me | Theorems.Thm_PDivisibleGroup_Tower_surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
-- name    : PDivisibleGroup.Tower.surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/5cd984d3-9202-55a7-aa2c-421b3f1d346a
-- title:
--   Split idempotent subtower of a p-divisible tower over 𝔽ₚ
-- statement:
--   Fix a prime $p$ and a natural number $h$. Let $B : \mathbb{N} \to \mathrm{Type}$ be a family of commutative rings, each carrying a Hopf algebra structure over $\mathbb{Z}/p$ whose comultiplication is cocommutative and which is finite as a $\mathbb{Z}/p$-module, let $s_n : B(n+1) \to B(n)$ be bialgebra maps over $\mathbb{Z}/p$ that are surjective, and assume $\operatorname{finrank}_{\mathbb{Z}/p} B(n) = p^{nh}$ and that $\ker s_n$ is the $p^n$-torsion ideal of $B(n+1)$, that is, the image of the augmentation ideal $\ker(\text{counit})$ under [`PDivisibleGroup.Hopf.nsmulAlgHom`](def/PDivisibleGroup_Basic.html#L16) at $p^n$ (the $p^n$-th convolution power of the identity, i.e. multiplication by $p^n$ on the associated group scheme). Let $e_n : B(n) \to B(n)$ be bialgebra endomorphisms with $e_n \circ e_n = e_n$ and $s_n \circ e_{n+1} = e_n \circ s_n$. Let $C : \mathbb{N} \to \mathrm{Type}$ be a second such family of finite cocommutative commutative Hopf algebras over $\mathbb{Z}/p$, together with bialgebra maps $q_n : B(n) \to C(n)$ surjective and $i_n : C(n) \to B(n)$ satisfying $q_n \circ i_n = \mathrm{id}_{C(n)}$ and $i_n \circ q_n = e_n$. The conclusion is the conjunction of three assertions about the transition maps $t_n := q_n \circ s_n \circ i_{n+1} : C(n+1) \to C(n)$: each $t_n$ is surjective; there is a single $h_1 \le h$ with $\operatorname{finrank}_{\mathbb{Z}/p} C(n) = p^{n h_1}$ for all $n$; and $\ker t_n$ equals the $p^n$-torsion ideal of $C(n+1)$ in the same sense as above.
--
--   This is the statement that a direct factor cut out by an idempotent endomorphism of a $p$-divisible group over $\mathbb{F}_p$ is again $p$-divisible, of height at most that of the ambient group: the split subtower $(C_n, t_n)$ satisfies exactly Tate's axioms as recorded in the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199) (freeness over the field $\mathbb{Z}/p$ being automatic from finiteness). It is used to transfer the tower results over $\mathbb{F}_p$ to the factor cut out by an idempotent, in the proof of [`PDivisibleGroup.forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung`](thm.html#PDivisibleGroup.forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Tower_surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.Tower.surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra (ZMod p) (B n)]
    [∀ n, Coalgebra.IsCocomm (ZMod p) (B n)] [∀ n, Module.Finite (ZMod p) (B n)]
    (s : ∀ n, B (n + 1) →ₐc[ZMod p] B n) (hs : ∀ n, Function.Surjective (s n))
    (hrankB : ∀ n, Module.finrank (ZMod p) (B n) = p ^ (n * h))
    (hkerB : ∀ n, RingHom.ker (s n) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (B (n + 1)) (p ^ n))

    (e : ∀ n, B n →ₐc[ZMod p] B n) (he : ∀ n, (e n).comp (e n) = e n)
    (het : ∀ n, (s n).comp (e (n + 1)) = (e n).comp (s n))
    (C : ℕ → Type) [∀ n, CommRing (C n)] [∀ n, HopfAlgebra (ZMod p) (C n)]
    [∀ n, Coalgebra.IsCocomm (ZMod p) (C n)] [∀ n, Module.Finite (ZMod p) (C n)]
    (q : ∀ n, B n →ₐc[ZMod p] C n) (i : ∀ n, C n →ₐc[ZMod p] B n)
    (hq : ∀ n, Function.Surjective (q n))
    (hqi : ∀ n, (q n).comp (i n) = BialgHom.id (ZMod p) (C n))
    (hiq : ∀ n, (i n).comp (q n) = e n) :
    (∀ n, Function.Surjective ((q n).comp ((s n).comp (i (n + 1))))) ∧
    (∃ h₁ : ℕ, h₁ ≤ h ∧ ∀ n, Module.finrank (ZMod p) (C n) = p ^ (n * h₁)) ∧
    (∀ n, RingHom.ker ((q n).comp ((s n).comp (i (n + 1)))) =
      PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (C (n + 1)) (p ^ n)) := by sorry
