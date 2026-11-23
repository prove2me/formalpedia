-- Prove2me | Theorems.Thm_PalomaMax2SAT_UgcClass_ugc_class
-- name    : PalomaMax2SAT.UgcClass.ugc_class
-- status  : Proved
-- author  : @vegafrank
-- created : 2026-11-23T04:39:19.402879+00:00
-- url     : https://prove2.me/theorems/0af5de5e-cc87-4f6b-89b1-c3728ad25ff4
-- title:
--   The cut-to-formula pipeline exceeds the Unique Games thresholds (83/84 on the three-occurrence Horn class)
-- statement:
--   Let $\beta^\star=0.94016567$ and $\alpha^*=0.94615981$ be the Unique Games thresholds for MAX 2-SAT and weighted MAX-$\{1,2\}$-HORN-SAT; then $\beta^\star<\alpha^*<\tfrac{83}{84}$. Let $G$ be a graph with $n$ vertices and $m$ edges given by its edge list, and let $H(G)$ be the conflict graph of the MAX 2-SAT formula $F_G$ (edge clauses $x_u\vee x_v$ and $\neg x_u\vee\neg x_v$), whose vertices are the $4m$ literal occurrences. (1) For every vertex set $S$, the occurrences selected by $S$ form an independent set of $H(G)$ of size $m+\operatorname{cut}(S)$. (2) If $\operatorname{maxcut}(G)=c^*$ then $\alpha(H(G))=m+c^*$. (3) If every vertex of $G$ has degree $d$, then $H(G)$ is $(d+1)$-regular, and $H(G)$ always has $4m$ vertices. (4) If $c\le m$ and $8785\,c\le10000\,\mathrm{cut}$ then $18785\,(m+c)\le20000\,(m+\mathrm{cut})$. (5) For every $D\ge1$, every $D$-regular graph $H$ with a port labelling, on $n$ vertices and $m$ edges with independence number $\alpha$, and every independent set $I$ with $18785\,\alpha\le20000\,|I|$, the assignment obtained from $I$ satisfies $84\cdot\operatorname{sat}(T_H)\ge83\,((D+1)n+m+\alpha)$, i.e. at least $83/84$ of the optimum of the three-occurrence Horn formula $T_H$. A Goemans--Williamson cut has $\mathrm{cut}\ge0.8785\,c^*$, so (1)--(5) turn it into the hypothesis of (5), which is how Theorem `thm:ugc-class` reaches $83/84$. The Goemans--Williamson guarantee, the polynomial running time and the Unique Games hardness thresholds are cited in the paper and are not formalized; the Unique Games thresholds quantify over all instances, so the statement is consistent with the Unique Games Conjecture.
-- source:
--   https://github.com/frankvegadelgado/paloma/blob/c98d15fc9b5de5a8d2392e71ef5a45e7c68ecb0f/doc/paper.tex#L348

import Mathlib
import Definitions.Def_PalomaMax2SAT_UgcClass_Defs

theorem PalomaMax2SAT.UgcClass.ugc_class :
    ((94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
      (94615981 : ℚ) / 100000000 < 83 / 84) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (S : Finset (Fin n)),
      PalomaMax2SAT.ConflictGraph.Ind G (PalomaMax2SAT.ConflictGraph.selSet G S) ∧
        (PalomaMax2SAT.ConflictGraph.selSet G S).card =
          m + PalomaMax2SAT.CutTransfer.cutCount G S) ∧
    (∀ {n m mc : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m),
      PalomaMax2SAT.ConflictGraph.IsMaxCut G mc →
        PalomaMax2SAT.ConflictGraph.IsIndNumber G (m + mc)) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (d : ℕ),
      (∀ v, PalomaMax2SAT.ConflictDegree.occ G v = d) →
        ∀ p : PalomaMax2SAT.ConflictGraph.Occ m,
          (PalomaMax2SAT.ConflictDegree.nbrs G p).card = d + 1) ∧
    (∀ m : ℕ, Fintype.card (PalomaMax2SAT.ConflictGraph.Occ m) = 4 * m) ∧
    (∀ m c cut : ℕ, c ≤ m → 8785 * c ≤ 10000 * cut →
      18785 * (m + c) ≤ 20000 * (m + cut)) ∧
    ∀ {D n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph D n m) (_ : 0 < D)
      (_ : PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha)
      (I : Finset (Fin n)) (_ : PalomaMax2SAT.DegreeFormula.Independent G I)
      (_ : 18785 * alpha ≤ 20000 * I.card),
      83 * ((D + 1) * n + m + alpha) ≤
        84 * PalomaMax2SAT.DegreeFormula.satCount G
          (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
            Fin n → Fin (D + 1) → Bool) := by sorry
