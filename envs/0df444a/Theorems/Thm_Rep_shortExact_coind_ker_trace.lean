-- Prove2me | Theorems.Thm_Rep_shortExact_coind_ker_trace
-- name    : Rep.shortExact_coind_ker_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/8a8dcf06-34ce-5f52-9353-57c2df2b3073
-- title:
--   Exactness of coinduction from a finite-index subgroup and of its trace kernels
-- statement:
--   Let $k$ be a field, $G$ a group and $U \le G$ a subgroup of finite index, and let $A, B, C$ be $k$-linear representations of $G$ equipped with morphisms $\alpha \colon A \to B$, $\beta \colon B \to C$ such that $\alpha$ is injective on underlying modules, $\beta$ is surjective, and for every $b \in B$ one has $\beta(b) = 0$ if and only if $b$ lies in the image of $\alpha$. Write $Y_X = \mathrm{coind}_{U \hookrightarrow G}\,\mathrm{res}_{U \hookrightarrow G}\,X$ for $X = A, B, C$. Assume given morphisms $\tau_X \colon Y_X \to X$ with $\tau_X(y) = \sum_{c \in G/U} X.\rho(\bar c)\,y(\bar c^{-1})$, the finite sum being over the cosets with $\bar c$ a chosen representative of $c$; morphisms $i_X \colon K_X \to Y_X$ that are injective on underlying modules and whose image is exactly the set of $y$ with $\tau_X(y) = 0$; morphisms $Y_\alpha \colon Y_A \to Y_B$ and $Y_\beta \colon Y_B \to Y_C$ acting pointwise by $\alpha$ respectively $\beta$; and morphisms $K_\alpha \colon K_A \to K_B$, $K_\beta \colon K_B \to K_C$ with $K_\alpha$ followed by $i_B$ equal to $i_A$ followed by $Y_\alpha$, and $K_\beta$ followed by $i_C$ equal to $i_B$ followed by $Y_\beta$. Then $Y_\alpha$ is injective, $Y_\beta$ is surjective, and $Y_\beta(y) = 0$ exactly when $y \in \mathrm{im}\,Y_\alpha$; and likewise $K_\alpha$ is injective, $K_\beta$ is surjective, and $K_\beta(y) = 0$ exactly when $y \in \mathrm{im}\,K_\alpha$.
--
--   This is the exactness of coinduction from a finite-index subgroup, together with the exactness of the sequence of kernels of the trace maps $\tau_X \colon \mathrm{coind}\,\mathrm{res}\,X \to X$, stated in elementwise form for representations of an abstract group. It is used in the comparison of second cohomology groups, namely in the proof that the induced map on continuous $H^2$ is surjective when the map of coefficients is.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_coind_ker_trace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory

theorem Rep.shortExact_coind_ker_trace {k G : Type u} [Field k] [Group G]
    (U : Subgroup G) [U.FiniteIndex]
    {A B C : Rep.{u} k G} (α : A ⟶ B) (β : B ⟶ C)
    (hα : Function.Injective α.hom) (hβ : Function.Surjective β.hom) (hex : ∀ b : B, β.hom b = 0 ↔ ∃ a : A, α.hom a = b)
    (τA : Rep.coind U.subtype (Rep.res U.subtype A) ⟶ A) (τB : Rep.coind U.subtype (Rep.res U.subtype B) ⟶ B) (τC : Rep.coind U.subtype (Rep.res U.subtype C) ⟶ C)
    (hτA : ∀ y : Rep.coind U.subtype (Rep.res U.subtype A), τA.hom y = ∑ᶠ c : G ⧸ U, A.ρ c.out ((y : G → A) (c.out)⁻¹))
    (hτB : ∀ y : Rep.coind U.subtype (Rep.res U.subtype B), τB.hom y = ∑ᶠ c : G ⧸ U, B.ρ c.out ((y : G → B) (c.out)⁻¹))
    (hτC : ∀ y : Rep.coind U.subtype (Rep.res U.subtype C), τC.hom y = ∑ᶠ c : G ⧸ U, C.ρ c.out ((y : G → C) (c.out)⁻¹))
    {KA KB KC : Rep.{u} k G} (iA : KA ⟶ Rep.coind U.subtype (Rep.res U.subtype A)) (iB : KB ⟶ Rep.coind U.subtype (Rep.res U.subtype B)) (iC : KC ⟶ Rep.coind U.subtype (Rep.res U.subtype C))
    (hiA : Function.Injective iA.hom) (hτiA : ∀ y : Rep.coind U.subtype (Rep.res U.subtype A), τA.hom y = 0 ↔ ∃ κ : KA, iA.hom κ = y)
    (hiB : Function.Injective iB.hom) (hτiB : ∀ y : Rep.coind U.subtype (Rep.res U.subtype B), τB.hom y = 0 ↔ ∃ κ : KB, iB.hom κ = y)
    (hiC : Function.Injective iC.hom) (hτiC : ∀ y : Rep.coind U.subtype (Rep.res U.subtype C), τC.hom y = 0 ↔ ∃ κ : KC, iC.hom κ = y)
    (Yα : Rep.coind U.subtype (Rep.res U.subtype A) ⟶ Rep.coind U.subtype (Rep.res U.subtype B)) (Yβ : Rep.coind U.subtype (Rep.res U.subtype B) ⟶ Rep.coind U.subtype (Rep.res U.subtype C))
    (hYα : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype A)) (g : G), ((Yα.hom y : Rep.coind U.subtype (Rep.res U.subtype B)) : G → B) g = α.hom ((y : G → A) g))
    (hYβ : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype B)) (g : G), ((Yβ.hom y : Rep.coind U.subtype (Rep.res U.subtype C)) : G → C) g = β.hom ((y : G → B) g))
    (Kα : KA ⟶ KB) (Kβ : KB ⟶ KC) (hKα : Kα ≫ iB = iA ≫ Yα) (hKβ : Kβ ≫ iC = iB ≫ Yβ) :
    (Function.Injective Yα.hom ∧ Function.Surjective Yβ.hom ∧ ∀ y : Rep.coind U.subtype (Rep.res U.subtype B), Yβ.hom y = 0 ↔ ∃ x : Rep.coind U.subtype (Rep.res U.subtype A), Yα.hom x = y) ∧
    (Function.Injective Kα.hom ∧ Function.Surjective Kβ.hom ∧ ∀ y : KB, Kβ.hom y = 0 ↔ ∃ x : KA, Kα.hom x = y) := by sorry
