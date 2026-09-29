-- Prove2me | Theorems.Thm_PDivisibleGroup_formallyEtale_level_of_hasDimension_zero
-- name    : PDivisibleGroup.formallyEtale_level_of_hasDimension_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/72434de6-55ff-5dc0-a90e-809a33268ab7
-- title:
--   Dimension zero p-divisible groups have formally étale levels
-- statement:
--   Let $R$ be a commutative ring, let $p$ and $h$ be natural numbers, and let $G$ be a $p$-divisible group over $R$ of height data $(p,h)$ in the sense of the project structure: a family of types `G.level v` ($v\in\mathbb N$), each a commutative ring carrying a cocommutative Hopf algebra structure over $R$ and finite and free as an $R$-module, together with surjective coalgebra-and-algebra maps $\mathrm{transition}_v\colon \mathcal O_{v+1}\to\mathcal O_v$ whose kernel is the ideal obtained by pushing the augmentation ideal of $\mathcal O_{v+1}$ forward along multiplication by $p^{v}$, and with $\operatorname{rank}_R \mathcal O_v = p^{v h}$ for all $v$. Assume $G$ has dimension $0$ in the sense of the project predicate: for every $v$ there is an $R$-linear isomorphism from the cotangent module $I_v/I_v^2$ of the augmentation ideal $I_v$ of $\mathcal O_v$ onto the module of functions $\mathrm{Fin}\,0 \to R/(p^{v})$, that is, this cotangent module vanishes. Then for every $v$ the $R$-algebra `G.level v` is formally étale.
--
--   This is the implication '$\dim G = 0$ implies the level algebras are étale', the infinitesimal half of the statement that a $p$-divisible group with vanishing cotangent is étale; no hypothesis on the base ring $R$ is imposed. It feeds the deduction that unramifiedness of the Tate module representation forces the levels to be étale over a ring of integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_formallyEtale_level_of_hasDimension_zero.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Dimension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.formallyEtale_level_of_hasDimension_zero
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (hG : G.HasDimension 0) (v : ℕ) :
    Algebra.FormallyEtale R (G.level v) := by sorry
