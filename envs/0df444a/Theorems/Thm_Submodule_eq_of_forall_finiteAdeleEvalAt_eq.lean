-- Prove2me | Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
-- name    : Submodule.eq_of_forall_finiteAdeleEvalAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/e746fd01-e4dc-59f7-83cd-73184e04a8ba
-- title:
--   Finite adelic elements are determined by their local components
-- statement:
--   Let $D$ be a ring equipped with a $\mathbb{Q}$-algebra structure that is finite-dimensional as a $\mathbb{Q}$-module, and let $x, y$ be elements of the tensor product $D \otimes_{\mathbb{Q}} \mathbb{A}_{\mathbb{Q}}^{f}$, where $\mathbb{A}_{\mathbb{Q}}^{f}$ is the finite adele ring of $\mathbb{Q}$ relative to the ring of integers $\mathcal{O}_{\mathbb{Q}}$, realised as a restricted product of the $v$-adic completions over the height-one primes $v$ of $\mathcal{O}_{\mathbb{Q}}$. For each such $v$, the map [`Submodule.finiteAdeleEvalAt`](def/Submodule_LocalBox.html#L36) is the $\mathbb{Q}$-algebra homomorphism $D \otimes_{\mathbb{Q}} \mathbb{A}_{\mathbb{Q}}^{f} \to D \otimes_{\mathbb{Q}} \mathbb{Q}_v$ obtained by tensoring the identity of $D$ with the evaluation-at-$v$ ring homomorphism of the restricted product (viewed as a $\mathbb{Q}$-algebra map into the $v$-adic completion $\mathbb{Q}_v$). The hypothesis is that for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the images of $x$ and $y$ under this map agree in $D \otimes_{\mathbb{Q}} \mathbb{Q}_v$. The conclusion is that $x = y$. Equivalently, the product of the local component maps on $D \otimes_{\mathbb{Q}} \mathbb{A}_{\mathbb{Q}}^{f}$ is injective.
--
--   This is the injectivity half of the local–global description of the finite adelic algebra $\widehat{D} = D \otimes_{\mathbb{Q}} \mathbb{A}_{\mathbb{Q}}^{f}$ of a finite-dimensional $\mathbb{Q}$-algebra as a restricted product of its completions $D \otimes_{\mathbb{Q}} \mathbb{Q}_v$. It belongs to the local vocabulary used for place-by-place arguments about orders and lattices in quaternion algebras, and is invoked by the statements about Eichler orders and level structures in the Čerednik–Drinfeld tower that reduce an adelic identity to its local components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq.lean

import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.eq_of_forall_finiteAdeleEvalAt_eq
    {D : Type*} [Ring D] [Algebra ℚ D] [Module.Finite ℚ D]
    (x y : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt D v x = Submodule.finiteAdeleEvalAt D v y) :
    x = y := by sorry
