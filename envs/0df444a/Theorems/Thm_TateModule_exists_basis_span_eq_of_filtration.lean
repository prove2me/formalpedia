-- Prove2me | Theorems.Thm_TateModule_exists_basis_span_eq_of_filtration
-- name    : TateModule.exists_basis_span_eq_of_filtration
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/c1074545-d9ce-5717-ac13-f833c326fa9a
-- title:
--   A compatible filtration cuts out a line in a Tate module
-- statement:
--   Let $M$ be an additive abelian group and $p$ a prime. Assume that for every $n$ the $p^n$-torsion subgroup $M[p^n] = \{x \in M : p^n x = 0\}$ (the $\mathbb{Z}$-module torsion submodule `torsionBy ℤ M (p^n)`) is finite of cardinality $(p^n)^2$. Write $T_pM$ for [`TateModule p M`](def/EllipticCurve_TateModule.html#L15), the subgroup of sequences $x : \mathbb{N} \to M$ such that $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$, viewed as a module over $\mathbb{Z}_p$. Let $P$ be a predicate on $M$ and $F : \mathbb{N} \to$ (subgroups of $M$) a family such that for every $m \ge 1$ and every $x \in M$ one has $x \in F_m$ if and only if $p^m x = 0$ and $P(x)$ holds, and such that $F_m$ is finite of cardinality $p^m$ for every $m \ge 1$ (no condition is imposed on $F_0$). Let $L$ be a $\mathbb{Z}_p$-submodule of $T_pM$ whose members are exactly the compatible systems $x$ with $x_m \in F_m$ for all $m \ge 1$. Then there is a basis $b$ of $T_pM$ indexed by `Fin 2` over $\mathbb{Z}_p$ with $L = \mathbb{Z}_p \cdot b_0$, the $\mathbb{Z}_p$-span of the first basis vector.
--
--   This is the algebraic mechanism producing a rank-one free direct summand of a rank-two Tate module from a levelwise compatible family of subgroups of order $p^m$ in the $p^m$-torsion: the line $L$ is a direct summand, being spanned by a member of a basis. It is used in the construction of the decomposition characters attached to the Tate module of an ordinary point, via [`ModularCurve.exists_decompositionCharacters_multiplicativeSubmodule_cornerSubmodule_tateModule_jH_of_ordinary`](thm.html#ModularCurve.exists_decompositionCharacters_multiplicativeSubmodule_cornerSubmodule_tateModule_jH_of_ordinary); the statement itself involves no curve and no Galois action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_exists_basis_span_eq_of_filtration.lean

import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing Submodule

theorem TateModule.exists_basis_span_eq_of_filtration
    {M : Type} [AddCommGroup M] {p : ℕ} [Fact p.Prime]
    (hcard : ∀ n, Nat.card (torsionBy ℤ M ((p^n : ℕ) : ℤ)) = (p^n)^2)
    (F : ℕ → AddSubgroup M) (P : M → Prop)
    (hFiff : ∀ m, 1 ≤ m → ∀ x, x ∈ F m ↔ ((p^m : ℕ) : ℤ) • x = 0 ∧ P x)
    (hFcard : ∀ m, 1 ≤ m → Nat.card (F m) = p^m)
    (L : Submodule ℤ_[p] (TateModule p M))
    (hL : ∀ x, x ∈ L ↔ ∀ m, 1 ≤ m → (x : ℕ → M) m ∈ F m) :
    ∃ b : Module.Basis (Fin 2) ℤ_[p] (TateModule p M), L = ℤ_[p] ∙ b 0 := by sorry
