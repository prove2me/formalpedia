-- Prove2me | Theorems.Thm_PhyloCSP_lemma_7_9
-- name    : PhyloCSP.lemma_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:23:46.516531+00:00
-- url     : https://prove2.me/theorems/f8b8997b-be03-4af1-be0c-dfd189ddde8e
-- title:
--   Lemma 7.9 — $\mathrm{Aut}(\mathcal F)$ is amenable
-- statement:
--   The automorphism group $\mathrm{Aut}(\mathcal F)$ of the Fraïssé limit of finite binary tree structures, with the topology of pointwise convergence, is amenable: whenever it acts continuously on a nonempty compact Hausdorff space $Y$, there is an invariant Borel probability measure on $Y$.
--
--   Amenability is what allows the proof of Theorem 3.2(i) to average a random relation over $\mathrm{Aut}(\mathcal F)$ without losing any guarantee. The paper derives it from the criterion of Angel, Kechris and Lyons (Appendix B.2).
--
--   Differences from the source:
--   - encoding: compact Hausdorff spaces Y of any size → Y ranging over Type (the first universe); reason: for a group in Type the relevant compact spaces (e.g. the universal minimal flow) can be taken in Type
--   - encoding: Aut(F) of the abstract Fraïssé limit → the automorphism group of the concrete (Z, C), topology induced from the product of discrete topologies on Z^Z; reason: Theorem 7.4 / Appendix B.1 identify the concrete structure with F; basic neighborhoods agree
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Lemma 7.9, p.22 (PDF p.24); Section 7.3, p.22

import Mathlib
import Definitions.Def_PhyloCSP_AutF
import Definitions.Def_PhyloCSP_IsAmenable

set_option autoImplicit false

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Lemma 7.9, p.22 (PDF p.24): "The topological group
Aut(F) is amenable."

**Formalization Note.** `Aut(F)` is the automorphism group of the concrete Fraïssé limit
`(Z, fraisseRel)` with the topology of pointwise convergence (its topological-group structure is
proved in `Def_PhyloCSP_AutF`); amenability is the fixed-point property for continuous actions on
nonempty compact Hausdorff spaces (`IsAmenable`). -/
theorem lemma_7_9 : IsAmenable AutF := by sorry

end PhyloCSP
