-- Prove2me | Theorems.Thm_RepTheory_IsometricRep_exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors
-- name    : RepTheory.IsometricRep.exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/f6e7daf2-1403-57f4-8383-465068a8f586
-- title:
--   Admissible vectors force an isotypic irreducible smooth quotient
-- statement:
--   Let $G$ be a group carrying a topology in which multiplication is separately continuous, and let $H$ be a complex Hilbert space. Let $\rho : G \to \operatorname{End}_{\mathbb C}(H)$ be a group homomorphism into the $\mathbb C$-linear endomorphisms of $H$ such that $\langle \rho(g)x, \rho(g)y\rangle = \langle x,y\rangle$ for all $g \in G$ and $x,y \in H$. Let $S$ be a set of continuous $\mathbb C$-linear operators on $H$ with $s(\rho(g)x) = \rho(g)(s x)$ for all $s \in S$, $g \in G$, $x \in H$. Assume that every closed $\mathbb C$-subspace $W \subseteq H$ that is stable under all $\rho(g)$ and all $s \in S$ is $\bot$ or $\top$, and that there exists a $\rho$-stable subspace $X \subseteq H$ such that $X \cap H^K$ is finite-dimensional over $\mathbb C$ for every compact open subgroup $K \le G$, where $H^K$ denotes the vectors fixed by every $\rho(u)$, $u \in K$, and such that $X \cap H^{K_0} \neq \bot$ for at least one compact open subgroup $K_0$. The conclusion asserts the existence of a complex vector space $E$ (in the same universe as $H$) and a homomorphism $\pi_E : G \to \operatorname{End}_{\mathbb C}(E)$ which is irreducible ($E$ has a non-zero vector and every $\pi_E$-stable subspace, with no closedness required, is $\bot$ or $\top$), smooth (each vector of $E$ has open stabiliser $\{g : \pi_E(g)v = v\}$), and admissible (the $\pi_E$-fixed subspace of every compact open subgroup is finite-dimensional), such that for every compact open subgroup $K \le G$ there are $d \in \mathbb N$ and vectors $e_0,\dots,e_{d-1} \in E$ with: for every $x \in H$ fixed by all $\rho(k)$, $k \in K$, and every finitely supported $\mu : G \to \mathbb C$, if $\sum_h \mu(h)\,\pi_E(h)e_j = 0$ for every $j$, then $\sum_h \mu(h)\,\rho(h)x = 0$.
--
--   The statement extracts from an irreducible isometric Hilbert-space representation possessing an admissible stable subspace an irreducible smooth admissible representation $E$ whose group-algebra annihilators of finite families of vectors kill all $K$-fixed vectors of $H$; in other words the smooth part of $H$ is $E$-isotypic, in the style of the discreteness arguments for spaces of cusp forms. It is used in the cubic induction step of the Langlands–Tunnell input, through [`LanglandsTunnell.CubicInduction.exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RepTheory_IsometricRep_exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors.lean

import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FLT.SmoothAdmissibleSchurCommutant
open scoped InnerProductSpace

universe v w

theorem RepTheory.IsometricRep.exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors
    {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* Module.End ℂ H) (hρ : ∀ (g : G) (x y : H), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (S : Set (H →L[ℂ] H)) (hS : ∀ s ∈ S, ∀ (g : G) (x : H), s (ρ g x) = ρ g (s x))
    (hirr : ∀ W : Submodule ℂ H, IsClosed (W : Set H) →
      (∀ (g : G) (x : H), x ∈ W → ρ g x ∈ W) → (∀ s ∈ S, ∀ x : H, x ∈ W → s x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hX : ∃ X : Submodule ℂ H, (∀ (g : G) (x : H), x ∈ X → ρ g x ∈ X) ∧
      (∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
        FiniteDimensional ℂ ↥(X ⊓ fixedVectors ρ K)) ∧
      ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G) ∧ X ⊓ fixedVectors ρ K₀ ≠ ⊥) :
    ∃ (E : Type w) (_ : AddCommGroup E) (_ : Module ℂ E) (πE : G →* Module.End ℂ E),
      IsIrreducibleRep πE ∧ IsSmoothRep πE ∧ IsAdmissibleRep πE ∧
        ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
          ∃ (d : ℕ) (e : Fin d → E), ∀ x : H, (∀ k ∈ K, ρ k x = x) → ∀ μ : G →₀ ℂ,
            (∀ j : Fin d, (μ.sum fun (h : G) (c : ℂ) => c • πE h (e j)) = 0) →
              (μ.sum fun (h : G) (c : ℂ) => c • ρ h x) = 0 := by sorry
