-- Prove2me | Theorems.Thm_Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span
-- name    : Subfield.exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/7d65b09c-0b08-541b-b34d-46c52da94398
-- title:
--   Finiteness of the integral closure one field up
-- statement:
--   Let $\Omega$ be a field of characteristic $0$, let $R$ be a subring of $\Omega$ whose underlying ring is noetherian, and let $F_0 \subseteq L$ be subfields of $\Omega$ with $R$ contained in $F_0$ (as subrings of $\Omega$). Assume every $x \in F_0$ admits $r, d \in R$ with $d \neq 0$ and $x d = r$, so that $F_0$ consists of quotients of elements of $R$. Let $N, B \subseteq \Omega$ be sets characterised by: $x \in N$ iff $x \in F_0$ and $x$ is integral over $R$, and $x \in B$ iff $x \in L$ and $x$ is integral over $R$. Assume further that there is a finite set $s \subseteq \Omega$ with $N$ contained in the $R$-submodule of $\Omega$ spanned by $s$, and a finite set $u \subseteq \Omega$ with $L$ contained in the $F_0$-submodule of $\Omega$ spanned by $u$ (so $L/F_0$ is finite). The conclusion is the existence of a finite set $t \subseteq B$ such that every $x \in B$ can be written as $x = \sum_{c \in t} f(c)\, c$ for some function $f : \Omega \to \Omega$ taking values in $N$ on $t$; that is, $B$ is generated as an $N$-module by $t$. (The coefficient function is only constrained at the points of $t$.)
--
--   This is the standard finiteness of integral closure in a finite separable extension, transposed to subobjects of a single ambient field of characteristic $0$: the integral closure $B$ of $R$ in $L$ is a finite module over the integral closure $N$ of $R$ in the base field $F_0$, provided the latter is already finite over $R$. It is used in the study of integral elements of the $\lambda$-field tower attached to the localisation at a node of a modular curve, where a finite module generating set for the integral elements over the base is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

theorem Subfield.exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span
    {Ω : Type*} [Field Ω] [CharZero Ω]
    (R : Subring Ω) (hR : IsNoetherianRing ↥R)
    (F₀ L : Subfield Ω) (hRF : R ≤ F₀.toSubring) (hFL : F₀ ≤ L)
    (hfrac : ∀ x ∈ F₀, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ x * d = r)
    (N B : Set Ω) (hN : ∀ x, x ∈ N ↔ x ∈ F₀ ∧ IsIntegral ↥R x) (hB : ∀ x, x ∈ B ↔ x ∈ L ∧ IsIntegral ↥R x)
    (s : Finset Ω) (hs : ∀ x ∈ N, x ∈ Submodule.span ↥R (↑s : Set Ω))
    (u : Finset Ω) (hu : ∀ x ∈ L, x ∈ Submodule.span ↥F₀ (↑u : Set Ω)) :
    ∃ t : Finset Ω, (↑t : Set Ω) ⊆ B ∧
      ∀ x ∈ B, ∃ f : Ω → Ω, (∀ c ∈ t, f c ∈ N) ∧ x = ∑ c ∈ t, f c * c := by sorry
