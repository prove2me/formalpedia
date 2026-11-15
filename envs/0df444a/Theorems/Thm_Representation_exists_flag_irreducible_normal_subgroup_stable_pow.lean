-- Prove2me | Theorems.Thm_Representation_exists_flag_irreducible_normal_subgroup_stable_pow
-- name    : Representation.exists_flag_irreducible_normal_subgroup_stable_pow
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T06:50:13.257551+00:00
-- url     : https://prove2.me/theorems/54e8f00f-f446-4649-80e9-d2722735e02a
-- title:
--   Clifford flag: for $\Gamma \trianglelefteq W$ and $f \in W$, a representation of $W$ has a flag with $\Gamma$-irreducible steps stable under some power $f^d$
-- statement:
--   Let $k$ be an algebraically closed field, $V$ a finite-dimensional $k$-vector space and $\sigma : W \to \mathrm{GL}(V)$ a representation of a group $W$. Let $\Gamma \trianglelefteq W$ be a normal subgroup and $f \in W$. Call a subspace $U \subseteq V$ $\Gamma$-stable if $\sigma(g)U \subseteq U$ for all $g \in \Gamma$.
--
--   Then there are an integer $d \ge 1$ and a flag of subspaces
--
--   $$0 = F_0 < F_1 < \cdots < F_r = V$$
--
--   such that
--
--   1. every $F_i$ is $\Gamma$-stable and stable under $\sigma(f^d)$;
--   2. every step is $\Gamma$-irreducible: if $U$ is $\Gamma$-stable and $F_i \subseteq U \subseteq F_{i+1}$, then $U = F_i$ or $U = F_{i+1}$ (equivalently, each $F_{i+1}/F_i$ is an irreducible representation of $\Gamma$).
--
--   So $V$ has a composition series as a $\Gamma$-representation that is also invariant under $\langle \Gamma, f^d \rangle$.
--
--   Role: for a lisse sheaf on a curve over a finite field ($W$ = the Weil group, $\Gamma$ = the geometric fundamental group, $f$ = a Frobenius element) this says that after a finite extension of the base field of degree $d$ the sheaf has a filtration by subsheaves whose graded pieces are geometrically irreducible; it is the reduction to geometrically irreducible sheaves in Deligne's theory of weights (Weil II), as presented by Katz.
--
--   **Formalization Note**: the representation is Mathlib's `Representation k W V`; $\Gamma$ is a `Subgroup W` with `[Γ.Normal]`. The flag is `F : ℕ → Submodule k V` with `F 0 = ⊥` and `F r = ⊤`; only the values `F i` for `i ≤ r` matter. Stability is written elementwise (`∀ g ∈ Γ, ∀ v ∈ F i, σ g v ∈ F i`), and irreducibility of the step $F_{i+1}/F_i$ is stated in $V$: `F i < F (i + 1)` and every $\Gamma$-stable `U` with `F i ≤ U ≤ F (i + 1)` equals one of the two ends. No hypothesis on $W$, $\Gamma$ or the characteristic of $k$ is needed; for $\Gamma$ trivial the statement gives a full flag stable under $\sigma(f^d)$, and for $\Gamma = W$ a composition series of $V$.
-- source:
--   A. H. Clifford, "Representations induced in an invariant subgroup", Ann. of Math. 38 (1937), 533–550 (Clifford's theorem); used in this form for lisse sheaves (Weil group $W$, geometric fundamental group $\Gamma$, Frobenius $f$) in N. M. Katz, "L-functions and monodromy: four lectures on Weil II", Adv. Math. 160 (2001), 81–132

import Mathlib

set_option autoImplicit false

theorem Representation.exists_flag_irreducible_normal_subgroup_stable_pow
    {k W V : Type*} [Field k] [IsAlgClosed k] [Group W] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (σ : Representation k W V) (Γ : Subgroup W) [Γ.Normal] (f : W) :
    ∃ d : ℕ, 0 < d ∧ ∃ r : ℕ, ∃ F : ℕ → Submodule k V, F 0 = ⊥ ∧ F r = ⊤ ∧
      (∀ i ≤ r, ∀ g ∈ Γ, ∀ v ∈ F i, σ g v ∈ F i) ∧
      (∀ i ≤ r, ∀ v ∈ F i, σ (f ^ d) v ∈ F i) ∧
      ∀ i < r, F i < F (i + 1) ∧
        ∀ U : Submodule k V, (∀ g ∈ Γ, ∀ v ∈ U, σ g v ∈ U) → F i ≤ U → U ≤ F (i + 1) →
          U = F i ∨ U = F (i + 1) := by sorry
