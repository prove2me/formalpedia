-- Prove2me | Theorems.Thm_Submodule_exists_invertible_quotient_and_forall_localized_eq
-- name    : Submodule.exists_invertible_quotient_and_forall_localized_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/d44ad79f-b6a5-5bed-867a-d13ca445feb7
-- title:
--   Gluing local submodules with invertible quotients
-- statement:
--   Let $R$ be a commutative ring and $V$ a finitely presented $R$-module. For each point $x$ of $\operatorname{Spec} R$, with prime $\mathfrak p_x = x.\mathtt{asIdeal}$, suppose given an $R$-module $V_x$ that is also a module over the localisation $R_{\mathfrak p_x} =$ `Localization.AtPrime` $\mathfrak p_x$ compatibly with the $R$-action, together with an $R$-linear map $f_x : V \to V_x$ which realises $V_x$ as the localisation of $V$ at the multiplicative set $\mathfrak p_x^{c}$ of elements outside $\mathfrak p_x$ (`IsLocalizedModule`). Suppose given, for each $x$, an $R_{\mathfrak p_x}$-submodule $\Lambda_x \subseteq V_x$ such that the quotient $V_x / \Lambda_x$ is an invertible $R_{\mathfrak p_x}$-module, and assume the family $(\Lambda_x)$ is locally induced by finitely generated global submodules: for every $x$ there exist $r \in R \setminus \mathfrak p_x$ and a finitely generated submodule $N \subseteq V$ such that for every prime $y$ with $r \notin \mathfrak p_y$, the localised submodule of $N$ inside $V_y$ along $f_y$ equals $\Lambda_y$. The conclusion is that there exists a single submodule $N \subseteq V$ with $V/N$ an invertible $R$-module and with the localisation of $N$ inside $V_x$ along $f_x$ equal to $\Lambda_x$ for every prime $x$.
--
--   This is Zariski gluing, in commutative-algebra form, for $R$-points of the Grassmannian of invertible quotients of $V$: a family of local submodules with invertible quotients which is locally cut out by finitely generated global submodules descends to a global submodule with invertible quotient. It is used in the construction of Drinfeld data in the Čerednik–Drinfeld part of the development, via [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isQuadrupleOf`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isQuadrupleOf), and it invokes [`Module.Invertible.of_localization_maximal`](thm.html#Module.Invertible.of_localization_maximal) to check invertibility of the global quotient from its localisations at maximal ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_exists_invertible_quotient_and_forall_localized_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Submodule.exists_invertible_quotient_and_forall_localized_eq
    {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] [Module.FinitePresentation R V]
    (Vₚ : PrimeSpectrum R → Type) [∀ x, AddCommGroup (Vₚ x)] [∀ x, Module R (Vₚ x)]
    [∀ x, Module (Localization.AtPrime x.asIdeal) (Vₚ x)]
    [∀ x, IsScalarTower R (Localization.AtPrime x.asIdeal) (Vₚ x)]
    (f : ∀ x, V →ₗ[R] Vₚ x) [∀ x, IsLocalizedModule x.asIdeal.primeCompl (f x)]
    (Λ : ∀ x, Submodule (Localization.AtPrime x.asIdeal) (Vₚ x))
    (hinv : ∀ x, Module.Invertible (Localization.AtPrime x.asIdeal) (Vₚ x ⧸ Λ x))
    (hloc : ∀ x : PrimeSpectrum R, ∃ r : R, r ∉ x.asIdeal ∧ ∃ N : Submodule R V, N.FG ∧
      ∀ y : PrimeSpectrum R, r ∉ y.asIdeal →
        Submodule.localized' (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl (f y) N = Λ y) :
    ∃ N : Submodule R V, Module.Invertible R (V ⧸ N) ∧
      ∀ x : PrimeSpectrum R, Submodule.localized' (Localization.AtPrime x.asIdeal) x.asIdeal.primeCompl (f x) N = Λ x := by sorry
