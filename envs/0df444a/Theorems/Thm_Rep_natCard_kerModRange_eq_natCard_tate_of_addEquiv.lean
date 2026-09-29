-- Prove2me | Theorems.Thm_Rep_natCard_kerModRange_eq_natCard_tate_of_addEquiv
-- name    : Rep.natCard_kerModRange_eq_natCard_tate_of_addEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/d54eaf5b-71a1-5982-ad1b-66655b3b3c94
-- title:
--   Tate ̂ H⁰ and ̂ H⁻¹ of a cyclic group on an additive model
-- statement:
--   Let $G$ be a finite group and $A$ a representation of $G$ over $\mathbb{Z}$ (an object of `Rep ℤ G`), and let $g\in G$ be such that every element of $G$ lies in the subgroup of integral powers of $g$, so that $G$ is cyclic with generator $g$. Let $X$ be an abelian group together with an isomorphism of additive groups $e\colon X\to A$ onto the underlying abelian group of $A$, and let $d,N\colon X\to X$ be additive endomorphisms pinned through $e$ by the formulas $e(d\,x)=\rho_A(g)(e\,x)-e\,x$ and $e(N\,x)=\sum_{i<\#G}\rho_A(g^i)(e\,x)$ for all $x\in X$, where $\#G$ is `Nat.card G`. Then two cardinality identities hold. First, the quotient of $\ker d$ by the subgroup $\operatorname{im}N\cap\ker d$ (the preimage of $\operatorname{im}N$ in $\ker d$) has the same cardinality as $A$'s `tateH0`, namely the quotient of the invariants $A^G$ by the image of the map $\overline{\mathrm{Nm}}$ induced on the coinvariants of $A$ by the norm $\sum_{h\in G}\rho_A(h)$ with values in the invariants. Second, the quotient of $\ker N$ by $\operatorname{im}d\cap\ker N$ has the same cardinality as `tateHneg1`, namely $\ker\overline{\mathrm{Nm}}$. Both cardinalities are `Nat.card`, with no finiteness assumption on $A$.
--
--   This is the standard computation of the Tate cohomology groups $\hat H^0(G,A)$ and $\hat H^{-1}(G,A)$ of a finite cyclic group as $\ker(g-1)/\operatorname{im}N$ and $\ker N/\operatorname{im}(g-1)$, packaged as a dictionary: a consumer working with an arbitrary additive model $X$ of $A$ and with its own endomorphisms $d$ and $N$ need only exhibit the comparison isomorphism $e$ and verify the two pinning formulas. It is used in the Herbrand-quotient computations for idele fibres, in [`M4aHerbrand.finSIdeleFibreBox_tateCard_eq_localDegreeProd`](thm.html#M4aHerbrand.finSIdeleFibreBox_tateCard_eq_localDegreeProd) and [`M4aHerbrand.infiniteIdeleFibre_tateCard_eq_localDegreeProd`](thm.html#M4aHerbrand.infiniteIdeleFibre_tateCard_eq_localDegreeProd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_natCard_kerModRange_eq_natCard_tate_of_addEquiv.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Rep

theorem Rep.natCard_kerModRange_eq_natCard_tate_of_addEquiv {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {X : Type} [AddCommGroup X] (e : X ≃+ A)
    (d : X →+ X) (hd : ∀ x, e (d x) = A.ρ g (e x) - e x)
    (N : X →+ X) (hN : ∀ x, e (N x) = ∑ i ∈ Finset.range (Nat.card G), A.ρ (g ^ i) (e x)) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker) = Nat.card A.tateH0 ∧
      Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = Nat.card A.tateHneg1 := by sorry
