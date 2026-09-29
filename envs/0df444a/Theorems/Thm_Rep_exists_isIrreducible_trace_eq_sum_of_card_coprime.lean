-- Prove2me | Theorems.Thm_Rep_exists_isIrreducible_trace_eq_sum_of_card_coprime
-- name    : Rep.exists_isIrreducible_trace_eq_sum_of_card_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/cf854281-1a12-5e5f-b011-df9d4ff6d890
-- title:
--   Semisimple trace decomposition over 𝔽ₚ in coprime order
-- statement:
--   Let $p$ be a prime (registered as such) and let $H$ be a finite group, carried by a type in the lowest universe, whose order is coprime to $p$. Then there exist a natural number $s$ and a family $T : \mathrm{Fin}\,s \to \mathrm{Rep}\,(\mathbb{Z}/p)\,H$ of representations of $H$ on $\mathbb{Z}/p$-modules in the lowest universe such that: (i) each $T j$ is finite-dimensional over $\mathbb{Z}/p$ and its representation $(T j).\rho$ is irreducible; (ii) the family is repetition-free in the sense that if $T i$ and $T j$ are isomorphic in the category $\mathrm{Rep}\,(\mathbb{Z}/p)\,H$ then $i = j$; and (iii) for every finite-dimensional $V$ in $\mathrm{Rep}\,(\mathbb{Z}/p)\,H$ there is a function $m : \mathrm{Fin}\,s \to \mathbb{N}$ with $\dim_{\mathbb{Z}/p} \operatorname{Hom}(T j, V) = m j \cdot \dim_{\mathbb{Z}/p} \operatorname{Hom}(T j, T j)$ for every $j$, the Hom-spaces being taken in $\mathrm{Rep}\,(\mathbb{Z}/p)\,H$, and such that for every $h \in H$ the trace of $V.\rho\,h$ on $V$ equals $\sum_j (m j) \cdot \operatorname{tr}((T j).\rho\,h)$ in $\mathbb{Z}/p$, the multiplicities being reduced modulo $p$.
--
--   This is Maschke semisimplicity together with Schur's lemma for $\mathbb{F}_p[H]$-modules when $p \nmid |H|$: a finite list of pairwise non-isomorphic irreducibles whose multiplicities in an arbitrary finite-dimensional $V$ are detected by dimensions of Hom-spaces and control the trace function of $V$ modulo $p$. It is used to turn integral multiplicity data into trace identities over $\mathbb{Z}/p$, and is cited by [`Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero`](thm.html#Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_isIrreducible_trace_eq_sum_of_card_coprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.exists_isIrreducible_trace_eq_sum_of_card_coprime
    {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H] (hH : (Nat.card H).Coprime p) :
    ∃ (s : ℕ) (T : Fin s → Rep.{0} (ZMod p) H),
      (∀ j, FiniteDimensional (ZMod p) (T j) ∧ (T j).ρ.IsIrreducible) ∧
      (∀ i j, Nonempty (T i ≅ T j) → i = j) ∧
      ∀ (V : Rep.{0} (ZMod p) H), FiniteDimensional (ZMod p) V →
        ∃ m : Fin s → ℕ, (∀ j, Module.finrank (ZMod p) (T j ⟶ V) = m j * Module.finrank (ZMod p) (T j ⟶ T j)) ∧
          ∀ h : H, LinearMap.trace (ZMod p) V (V.ρ h) =
            ∑ j, (m j : ZMod p) * LinearMap.trace (ZMod p) (T j) ((T j).ρ h) := by sorry
