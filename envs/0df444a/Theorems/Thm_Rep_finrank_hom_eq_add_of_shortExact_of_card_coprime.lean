-- Prove2me | Theorems.Thm_Rep_finrank_hom_eq_add_of_shortExact_of_card_coprime
-- name    : Rep.finrank_hom_eq_add_of_shortExact_of_card_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/a7cee17b-dba6-5ffd-bec8-1428ee340d55
-- title:
--   Additivity of dim Hom_H(T,-) in order prime to p
-- statement:
--   Let $p$ be a prime and let $H$ be a finite group whose order, taken as `Nat.card H`, is coprime to $p$. Let $T$ be an object of `Rep (ZMod p) H`, that is a $\mathbb{Z}/p$-linear representation of $H$ on a $\mathbb{Z}/p$-vector space (in universe $0$), assumed finite-dimensional over $\mathbb{Z}/p$. Let $X$ be a short complex $X_1 \to X_2 \to X_3$ in `Rep (ZMod p) H` which is short exact in the sense of `ShortComplex.ShortExact`, i.e. the first map is a monomorphism, the second is an epimorphism, and the complex is exact in the middle; assume moreover that $X_2$ is finite-dimensional over $\mathbb{Z}/p$. The conclusion is an identity of $\mathbb{Z}/p$-dimensions of the morphism spaces of the $\mathbb{Z}/p$-linear category `Rep (ZMod p) H`, i.e. of spaces of $H$-equivariant $\mathbb{Z}/p$-linear maps: $$\operatorname{finrank}_{\mathbb{Z}/p}(T \to X_2) = \operatorname{finrank}_{\mathbb{Z}/p}(T \to X_1) + \operatorname{finrank}_{\mathbb{Z}/p}(T \to X_3).$$ No separate finite-dimensionality hypothesis is imposed on $X_1$ or $X_3$.
--
--   This is the additivity of the functor $\operatorname{Hom}_H(T,-)$ on short exact sequences of $\mathbb{F}_p[H]$-modules when $p \nmid |H|$, a consequence of the semisimplicity of $\mathbb{F}_p[H]$ (Maschke). It is used, via [`Rep.eq_of_additive_of_forall_nonempty_res_iso`](thm.html#Rep.eq_of_additive_of_forall_nonempty_res_iso) and [`Rep.nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq`](thm.html#Rep.nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq), to propagate the invariants $V \mapsto \dim \operatorname{Hom}_H(T, V)$ along composition series and so to detect representations up to the relevant equivalence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_finrank_hom_eq_add_of_shortExact_of_card_coprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.finrank_hom_eq_add_of_shortExact_of_card_coprime
    {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H] (hH : (Nat.card H).Coprime p)
    (T : Rep.{0} (ZMod p) H) [FiniteDimensional (ZMod p) T]
    (X : ShortComplex (Rep.{0} (ZMod p) H)) (hX : X.ShortExact) [FiniteDimensional (ZMod p) X.X₂] :
    Module.finrank (ZMod p) (T ⟶ X.X₂) =
      Module.finrank (ZMod p) (T ⟶ X.X₁) + Module.finrank (ZMod p) (T ⟶ X.X₃) := by sorry
