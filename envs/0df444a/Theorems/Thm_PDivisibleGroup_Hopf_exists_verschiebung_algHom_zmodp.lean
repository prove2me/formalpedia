-- Prove2me | Theorems.Thm_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp
-- name    : PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/31aafcab-a779-5af2-9d1e-e816b46b663c
-- title:
--   Existence of the Verschiebung over 𝔽ₚ
-- statement:
--   Let $p$ be a prime and let $A$ be a commutative ring carrying the structure of a Hopf algebra over $\mathbb{Z}/p$ whose comultiplication is cocommutative and which is finite as a $\mathbb{Z}/p$-module. Write $[p]_A :=$ [`PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) A p`](def/PDivisibleGroup_Basic.html#L16) for the algebra endomorphism of $A$ obtained as the $p$-th convolution power of the identity map $\mathrm{id}_A$ (multiplication by $p$ on the associated group functor), and let [`CartierDual (ZMod p) A`](def/HopfAlgebra_CartierDual.html#L12) be the $\mathbb{Z}/p$-linear dual $A^{\vee} = \mathrm{Hom}_{\mathbb{Z}/p}(A,\mathbb{Z}/p)$ with its ring structure, so that $\varphi^p$ denotes the $p$-th convolution power of $\varphi \in A^{\vee}$. The assertion is that there exists a bialgebra endomorphism $V : A \to A$ over $\mathbb{Z}/p$ (a $\mathbb{Z}/p$-algebra map that is simultaneously a coalgebra map) such that: $(V a)^p = [p]_A(a)$ for all $a \in A$; $V(a^p) = [p]_A(a)$ for all $a \in A$; and $\varphi(V a) = (\varphi^p)(a)$ for all $\varphi \in A^{\vee}$ and all $a \in A$. No uniqueness claim is made, although the third identity determines $V$.
--
--   This is the existence of the Verschiebung $V$ on the coordinate ring of a finite commutative group scheme over $\mathbb{F}_p$: since the Frobenius twist is trivial over the prime field, the relative Frobenius is $a \mapsto a^p$ and the first two identities are $F \circ V = [p]$ and $V \circ F = [p]$, while the third exhibits $V$ as the transpose of the Frobenius of the Cartier dual. It is used in the analysis of Hopf algebras over $\mathbb{Z}/p$ with reduced Cartier dual and in the study of the $p$-power torsion levels attached to Néron models of modular curves at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v

theorem PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp
    (p : ℕ) [Fact p.Prime] (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A]
    [Coalgebra.IsCocomm (ZMod p) A] [Module.Finite (ZMod p) A] :
    ∃ V : A →ₐc[ZMod p] A,
      (∀ a, (V a) ^ p = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) A p a) ∧
      (∀ a, V (a ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) A p a) ∧
      (∀ (φ : CartierDual (ZMod p) A) (a : A), φ (V a) = (φ ^ p) a) := by sorry
