-- Prove2me | Theorems.Thm_P2mOS_defect_transport_cases
-- name    : P2mOS.defect_transport_cases
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/9d6eda7f-33d5-5e7f-bb6e-9a3013dd3272
-- title:
--   Transport of a square-zero cocycle defect under sorting
-- statement:
--   Let $S$ be a commutative ring, let $I$ be a linearly ordered type, and let $U, U' : I \to I \to S$ be two families satisfying $U_{pq}\,U'_{pq} = 1$ whenever $p < q$. For a map $f : \{0,1,2\} \to I$ write $T_{xy}$ for $U_{xy}$ if $x<y$, for $1$ if $x=y$, and for $U'_{yx}$ if $x>y$, and write $T'_{xy}$ for $U'_{xy}$ if $x<y$, for $1$ if $x=y$, and for $U_{yx}$ if $x>y$; the quantity of interest is the transported defect $T_{f0,f1}\,T_{f1,f2}\,T'_{f0,f2} - 1$. The theorem asserts two things simultaneously. First, if $f$ is not injective then this transported defect vanishes. Second, for every permutation $\sigma$ of $\{0,1,2\}$ such that $f \circ \sigma$ is strictly monotone, if the sorted defect $D := U_{f(\sigma 0)f(\sigma 1)}\,U_{f(\sigma 1)f(\sigma 2)}\,U'_{f(\sigma 0)f(\sigma 2)} - 1$ satisfies $D \cdot D = 0$, then the transported defect equals $\varepsilon(\sigma) \cdot D$, where the integer $\varepsilon(\sigma)$ is the sign of $\sigma$ acting by the integer scalar action on $S$.
--
--   This is the elementary ring-theoretic bookkeeping lemma showing that the $2$-cocycle defect of a family of lifted transition units, read off an unsorted triple of indices, agrees up to the sign of the sorting permutation with the defect read off the sorted triple, and vanishes when an index is repeated. It is used in the construction of the Picard obstruction cocycle for a small extension, where the sign-twisted sorted defect is the value prescribed on an ordered affine cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_P2mOS_defect_transport_cases.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem P2mOS.defect_transport_cases
    {S : Type*} [CommRing S] {I : Type*} [LinearOrder I]
    (U U' : I → I → S) (hUU' : ∀ p q, p < q → U p q * U' p q = 1) (f : Fin 3 → I) :
    (¬ Function.Injective f →
      (if f 0 < f 1 then U (f 0) (f 1) else if f 0 = f 1 then 1 else U' (f 1) (f 0)) *
        (if f 1 < f 2 then U (f 1) (f 2) else if f 1 = f 2 then 1 else U' (f 2) (f 1)) *
        (if f 0 < f 2 then U' (f 0) (f 2) else if f 0 = f 2 then 1 else U (f 2) (f 0)) - 1 = 0) ∧
    (∀ σ : Equiv.Perm (Fin 3), StrictMono (f ∘ σ) →
      (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1) *
        (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1) = 0 →
      (if f 0 < f 1 then U (f 0) (f 1) else if f 0 = f 1 then 1 else U' (f 1) (f 0)) *
        (if f 1 < f 2 then U (f 1) (f 2) else if f 1 = f 2 then 1 else U' (f 2) (f 1)) *
        (if f 0 < f 2 then U' (f 0) (f 2) else if f 0 = f 2 then 1 else U (f 2) (f 0)) - 1 =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) •
        (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1)) := by sorry
