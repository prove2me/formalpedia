-- Prove2me | Theorems.Thm_Representation_exists_submodule_quotient_line_of_commutator_le_of_isPGroup
-- name    : Representation.exists_submodule_quotient_line_of_commutator_le_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/9c2d3713-6662-5144-a947-a9e067f68619
-- title:
--   Simple quotient of an mathbb Fₚ[Γ]-module is an F-line
-- statement:
--   Let $p$ be a prime, let $\Gamma$ be a finite group, and let $P \le \Gamma$ be a normal subgroup which is a $p$-group, with the property that every commutator $a^{-1}b^{-1}ab$ ($a,b \in \Gamma$) lies in $P$; thus $\Gamma/P$ is abelian. Let $V$ be a finite, nontrivial module over $\mathbb{Z}/p$ and let $\rho$ be a representation of $\Gamma$ on $V$ over $\mathbb{Z}/p$. The assertion is that there exists a $\mathbb{Z}/p$-submodule $W \subseteq V$ which is stable under $\rho$, in the sense that $\rho(g)v \in W$ for all $g \in \Gamma$ and all $v \in W$, with $W \neq V$, and there exist a finite field $F$, an $F$-module structure on the quotient $V/W$, and a natural number $r > 0$, such that: $F$ has exactly $p^{r}$ elements; the $F$-action on $V/W$ is compatible with its additive structure in the sense that $(m : F) \cdot q = m \cdot q$ for every natural number $m$ and every $q \in V/W$; the $F$-dimension of $V/W$ is $1$; and for every $g \in \Gamma$ there is a scalar $a \in F$ with $\rho(g)v \equiv a\,(v \bmod W)$ in $V/W$ for all $v \in V$, i.e. $\Gamma$ acts on $V/W$ through scalars of $F$.
--
--   This is the group-representation core of Raynaud's analysis of the simple constituents of a finite commutative group scheme killed by $p$: a simple quotient of a finite $\mathbb F_p$-representation of a finite group whose commutator subgroup lies in a normal $p$-subgroup becomes a one-dimensional vector space over a finite field $F = \mathbb F_{p^r}$, with $\Gamma$ acting by $F$-scalars. It is used in the dévissage statement [`HopfAlgebra.hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField`](thm.html#HopfAlgebra.hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField), and it cites [`Representation.centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute`](thm.html#Representation.centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute), which identifies the commutant of a simple representation with commuting operators as a field acting transitively on nonzero vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_exists_submodule_quotient_line_of_commutator_le_of_isPGroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Representation.exists_submodule_quotient_line_of_commutator_le_of_isPGroup
    (p : ℕ) [Fact p.Prime]
    {Γ : Type u} [Group Γ] [Finite Γ] (P : Subgroup Γ) [P.Normal] (hP : IsPGroup p ↥P)
    (hcomm : ∀ a b : Γ, a⁻¹ * b⁻¹ * a * b ∈ P)
    {V : Type v} [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod p) Γ V) :
    ∃ W : Submodule (ZMod p) V, (∀ (g : Γ) (v : V), v ∈ W → ρ g v ∈ W) ∧ W ≠ ⊤ ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Module F (V ⧸ W)) (r : ℕ),
        0 < r ∧ Fintype.card F = p ^ r ∧
        (∀ (m : ℕ) (q : V ⧸ W), (m : F) • q = m • q) ∧
        Module.finrank F (V ⧸ W) = 1 ∧
        (∀ g : Γ, ∃ a : F, ∀ v : V, W.mkQ (ρ g v) = a • W.mkQ v) := by sorry
