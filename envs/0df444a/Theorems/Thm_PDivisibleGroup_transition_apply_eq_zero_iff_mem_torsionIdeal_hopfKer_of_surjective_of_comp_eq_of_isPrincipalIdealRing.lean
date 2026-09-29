-- Prove2me | Theorems.Thm_PDivisibleGroup_transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
-- name    : PDivisibleGroup.transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/840c39b1-f667-5214-b5fe-a41809c29647
-- title:
--   Kernel of transition on Hopf kernel is p^v-torsion ideal
-- statement:
--   Let $R$ be a local principal ideal domain with fraction field $K$ of characteristic zero (so $K$ is a field equipped with an $R$-algebra structure making it a fraction field of $R$), and let $p$ be a prime. Let $G$ and $T$ be $p$-divisible groups over $R$ of heights $h$ and $t$ in the project's sense: families of level algebras $G.\mathrm{level}\,v$, each a finite free cocommutative commutative Hopf $R$-algebra, together with surjective bialgebra transition maps $G.\mathrm{level}(v+1)\to G.\mathrm{level}\,v$, with $\operatorname{rank}_R G.\mathrm{level}\,v = p^{vh}$ and with the kernel of the $v$-th transition equal to the ideal $\mathrm{torsionIdeal}\,(p^v)$, that is the image of the augmentation ideal under $\mathrm{nsmulAlgHom}\,(p^v)$, the $p^v$-th convolution power of the identity. Let $\pi_v : G.\mathrm{level}\,v \to T.\mathrm{level}\,v$ be bialgebra maps, each surjective, compatible with the transitions in the sense that $\pi_{v+1}$ followed by $T$'s $v$-th transition equals $G$'s $v$-th transition followed by $\pi_v$. Fix $v$ and write $A = \mathrm{hopfKer}(\pi_{v+1})$ for the subalgebra of $G.\mathrm{level}(v+1)$ on which the coaction $(\mathrm{id}\otimes\pi_{v+1})\circ\Delta$ agrees with $a \mapsto a\otimes 1$; assume $A$ is flat over $R$, so that $A$ carries its Hopf algebra structure. Then for $a \in A$, the $v$-th transition map of $G$ kills $a$ if and only if $a$ lies in $\mathrm{torsionIdeal}\,R\,A\,(p^v)$, the image of the augmentation ideal of $A$ under the $p^v$-th convolution power of the identity of $A$.
--
--   This is the identity $B_v = B_{v+1}[p^v]$ for the quotient $B = G/T$ of a $p$-divisible group by a closed $p$-divisible subgroup, expressed on coordinate rings: the $p^v$-torsion ideal of the Hopf kernel of $\pi_{v+1}$ coincides with the part of it killed by the transition of $G$. It is the level-by-level compatibility check used in constructing the quotient $p$-divisible group, and is cited by [`PDivisibleGroup.exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing`](thm.html#PDivisibleGroup.exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (p : ℕ) [Fact p.Prime] {h t : ℕ} (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
    (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v))
    (v : ℕ) [Module.Flat R ↥(HopfAlgebra.hopfKer (π (v + 1)))]
    (a : ↥(HopfAlgebra.hopfKer (π (v + 1)))) :
    G.transition v (a : G.level (v + 1)) = 0 ↔
      a ∈ PDivisibleGroup.Hopf.torsionIdeal R ↥(HopfAlgebra.hopfKer (π (v + 1))) (p ^ v) := by sorry
