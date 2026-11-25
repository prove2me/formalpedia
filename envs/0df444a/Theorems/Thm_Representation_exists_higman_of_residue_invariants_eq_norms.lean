-- Prove2me | Theorems.Thm_Representation_exists_higman_of_residue_invariants_eq_norms
-- name    : Representation.exists_higman_of_residue_invariants_eq_norms
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T15:25:39.332931+00:00
-- url     : https://prove2.me/theorems/0798a38a-ea18-4933-bbd0-b21672eab600
-- title:
--   Cohomologically trivial implies projective (Rim, Serre): a free $R$-module with $G$-action and $\hat H^0(S, P/\mathfrak m P) = 0$ for a $p$-subgroup $S$ of index prime to $p$ is $R[G]$-projective
-- statement:
--   Let $R$ be a commutative local ring with maximal ideal $\mathfrak m$ whose residue field $k = R/\mathfrak m$ is finite of characteristic $p$ (for example $R = \mathbb Z/p^n\mathbb Z$, $R = \mathbb Z_p$, or $R = \mathbb F_q$). Let $G$ be a finite group and let $P$ be a finitely generated free $R$-module with an $R$-linear action $\rho$ of $G$. Let $S \le G$ be a $p$-subgroup whose index $[G : S]$ is prime to $p$ (for example a Sylow $p$-subgroup). Write $\bar P = k \otimes_R P \cong P/\mathfrak m P$ for the reduction, with the induced action of $G$, and assume that $\hat H^0(S, \bar P) = 0$, that is, every $S$-invariant vector of $\bar P$ is a norm:
--
--   $$x \in \bar P,\ s x = x \text{ for all } s \in S \implies x = \sum_{s \in S} s\, y \text{ for some } y \in \bar P .$$
--
--   Then there is an $R$-linear endomorphism $E$ of $P$ with
--
--   $$\sum_{g \in G} \rho(g) \circ E \circ \rho(g)^{-1} = \mathrm{id}_P .$$
--
--   This is Higman's criterion for projectivity: for a module $P$ that is projective over $R$, such an $E$ exists if and only if $P$ is a projective $R[G]$-module (given $E$, the map $v \mapsto \sum_g g \otimes E(g^{-1} v)$ is an $R[G]$-linear section of the multiplication map $R[G] \otimes_R P \to P$, whose source is $R[G]$-projective; conversely, if $P$ is a direct summand of a free $R[G]$-module, the projection onto the coefficient of $1 \in G$ provides $E$). So the theorem says: $P$ is a projective $R[G]$-module.
--
--   Role: this is the theorem of Rim and Serre that cohomologically trivial modules are projective, in the form needed for $\mathbb Z/\ell^n$-coefficients (modules free over $\mathbb Z/\ell^n$ with a finite group action, as in the Hattori-Stallings trace and Lefschetz-number arguments for perfect complexes of $\mathbb Z/\ell^n[G]$-modules in etale cohomology). Only one cohomological input is used: $\hat H^0$ of a single $p$-subgroup of index prime to $p$, on the reduction modulo $\mathfrak m$. The freeness of $P$ over $R$ cannot be dropped: for $G = 1$ every module is cohomologically trivial, but $\mathbb Z/p$ is not projective over $\mathbb Z/p^2$.
--
--   **Formalization Note**: `IsLocalRing.ResidueField R` is $k = R/\mathfrak m$ and `IsLocalRing.ResidueField R ⊗[R] P` is $\bar P = k \otimes_R P$; `(ρ s).baseChange (IsLocalRing.ResidueField R)` is the induced action $\mathrm{id}_k \otimes \rho(s)$ of $s$ on $\bar P$. `[Finite (IsLocalRing.ResidueField R)]` and `[CharP (IsLocalRing.ResidueField R) p]` say that $k$ is finite of characteristic $p$. The subgroup is `S : Subgroup G` with `IsPGroup p S` (every element has $p$-power order); `S.index` is $[G : S]$; `[Fintype S]` supplies the finite sum over $S$, and `s : S` is coerced to $G$ in `ρ s`. The hypothesis `hN` is $\hat H^0(S, \bar P) = 0$ (the image of the norm is always contained in the invariants, so only this inclusion is assumed). The conclusion is the Higman datum: `ρ g ∘ₗ E ∘ₗ ρ g⁻¹` is the composite $\rho(g) \circ E \circ \rho(g^{-1})$ and `LinearMap.id` is $\mathrm{id}_P$. All types are in `Type`.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer 1979, Chapter IX, Sections 5-6 (cohomologically trivial modules), doi:10.1007/978-1-4757-5673-9; D. S. Rim, Modules over finite groups, Ann. of Math. 69 (1959) 700-712, doi:10.2307/1970033; D. G. Higman, Indecomposable representations at characteristic p, Duke Math. J. 21 (1954) 377-381

import Mathlib

set_option autoImplicit false

open TensorProduct

theorem Representation.exists_higman_of_residue_invariants_eq_norms
    {R : Type} [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    {G : Type} [Group G] [Fintype G]
    {P : Type} [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    (ρ : Representation R G P) (S : Subgroup G) [Fintype S] (hS : IsPGroup p S)
    (hindex : ¬ p ∣ S.index)
    (hN : ∀ x : IsLocalRing.ResidueField R ⊗[R] P,
      (∀ s : S, (ρ s).baseChange (IsLocalRing.ResidueField R) x = x) →
        ∃ y : IsLocalRing.ResidueField R ⊗[R] P,
          x = ∑ s : S, (ρ s).baseChange (IsLocalRing.ResidueField R) y) :
    ∃ E : P →ₗ[R] P, ∑ g : G, ρ g ∘ₗ E ∘ₗ ρ g⁻¹ = LinearMap.id := by
  sorry
