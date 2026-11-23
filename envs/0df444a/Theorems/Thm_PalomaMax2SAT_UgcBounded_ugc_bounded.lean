-- Prove2me | Theorems.Thm_PalomaMax2SAT_UgcBounded_ugc_bounded
-- name    : PalomaMax2SAT.UgcBounded.ugc_bounded
-- status  : Proved
-- author  : @vegafrank
-- created : 2026-11-23T06:18:04.908182+00:00
-- url     : https://prove2.me/theorems/3ca93908-150c-4b65-9e9e-94d9884fe07a
-- title:
--   The cut-to-formula pipeline exceeds the Unique Games thresholds for bounded-degree graphs (0.9932 > 83/84)
-- statement:
--   Let $\beta^\star=0.94016567$ and $\alpha^*=0.94615981$ be the Unique Games thresholds for MAX 2-SAT and weighted MAX-$\{1,2\}$-HORN-SAT; then $\beta^\star<\alpha^*<\tfrac{83}{84}<0.9932$. Let $G$ be a graph with $n$ vertices and $m$ edges given by its edge list, and let $H(G)$ be the conflict graph of the MAX 2-SAT formula $F_G$ (edge clauses $x_u\vee x_v$ and $\neg x_u\vee\neg x_v$), whose vertices are the $4m$ literal occurrences. (1) For every vertex set $S$, the occurrences selected by $S$ form an independent set of $H(G)$ of size $m+\operatorname{cut}(S)$, and if $\operatorname{maxcut}(G)=c^*$ then $\alpha(H(G))=m+c^*$. (2) If every vertex of $G$ has degree at most $\Delta$, every vertex of $H(G)$ has degree at most $\Delta+1$. (3) For every $G$, the degrees of $H(G)$ add up to $4m+2\sum_v\deg_G(v)^2$, so $H(G)$ has $M\ge4m$ edges. (4) If $N=4m$, $B=N+3M$, $M\ge4m$, $\alpha\le2m$ and $18785\,\alpha\le20000\,s$, then $9932\,(B+\alpha)\le10000\,(B+s)$ and $83\,(B+\alpha)\le84\,(B+s)$. (5) For every graph $H$ with $n$ vertices and $m$ edges, degrees $d_v$ and a port labelling, the formula $T_H$ has $\sum_v d_v=2m$ and $\sum_v(d_v+1)+m=n+3m$; its optimum is $\sum_v(d_v+1)+m+\alpha(H)$, the lift of an independent set $I$ satisfies exactly $\sum_v(d_v+1)+m+|I|$ clauses, and if $8\alpha(H)\le\sum_v(d_v+1)+m$ and $18785\,\alpha(H)\le20000\,|I|$ the lift satisfies at least $9932/10000>83/84$ of the optimum. A Goemans--Williamson cut has $\mathrm{cut}\ge0.8785\,c^*$, which gives the hypothesis on $|I|$ through (1). The Goemans--Williamson guarantee, the polynomial running time, the identification of $T_{H(G)}$ with an instance of (5) and the Unique Games hardness thresholds are cited in the paper and are not formalized; the thresholds quantify over all instances, so the statement is consistent with the Unique Games Conjecture.
-- source:
--   https://github.com/frankvegadelgado/paloma/blob/191031e24787dadd84d6c28096c4e3141f9125be/doc/paper.tex#L336

import Mathlib
import Definitions.Def_PalomaMax2SAT_UgcBounded_Defs

theorem PalomaMax2SAT.UgcBounded.ugc_bounded :
    (((94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
        (94615981 : ℚ) / 100000000 < 83 / 84) ∧
      (83 : ℚ) / 84 < 9932 / 10000) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (S : Finset (Fin n)),
      PalomaMax2SAT.ConflictGraph.Ind G (PalomaMax2SAT.ConflictGraph.selSet G S) ∧
        (PalomaMax2SAT.ConflictGraph.selSet G S).card =
          m + PalomaMax2SAT.CutTransfer.cutCount G S) ∧
    (∀ {n m mc : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m),
      PalomaMax2SAT.ConflictGraph.IsMaxCut G mc →
        PalomaMax2SAT.ConflictGraph.IsIndNumber G (m + mc)) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (Dmax : ℕ),
      (∀ v, PalomaMax2SAT.ConflictDegree.occ G v ≤ Dmax) →
        ∀ p : PalomaMax2SAT.ConflictGraph.Occ m,
          (PalomaMax2SAT.ConflictDegree.nbrs G p).card ≤ Dmax + 1) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (M : ℕ),
      2 * M = ∑ p : PalomaMax2SAT.ConflictGraph.Occ m,
          (PalomaMax2SAT.ConflictDegree.nbrs G p).card →
        2 * M = 4 * m + 2 * ∑ v, PalomaMax2SAT.ConflictDegree.occ G v ^ 2 ∧ 4 * m ≤ M) ∧
    (∀ m M alpha s : ℕ, 4 * m ≤ M → alpha ≤ 2 * m → 18785 * alpha ≤ 20000 * s →
      9932 * ((4 * m + 3 * M) + alpha) ≤ 10000 * ((4 * m + 3 * M) + s) ∧
        83 * ((4 * m + 3 * M) + alpha) ≤ 84 * ((4 * m + 3 * M) + s)) ∧
    (∀ {n m : ℕ} {deg : Fin n → ℕ}
      (G : PalomaMax2SAT.GeneralDegreeFormula.GPortGraph n m deg),
      ∑ v, deg v = 2 * m ∧ ∑ v, (deg v + 1) + m = n + 3 * m) ∧
    (∀ {n m alpha : ℕ} {deg : Fin n → ℕ}
      (G : PalomaMax2SAT.GeneralDegreeFormula.GPortGraph n m deg),
      PalomaMax2SAT.GeneralDegreeFormula.IsIndependenceNumber G alpha →
        IsGreatest (Set.range (PalomaMax2SAT.GeneralDegreeFormula.satCount G))
          (∑ v, (deg v + 1) + m + alpha)) ∧
    ∀ {n m alpha : ℕ} {deg : Fin n → ℕ}
      (G : PalomaMax2SAT.GeneralDegreeFormula.GPortGraph n m deg)
      (_ : PalomaMax2SAT.GeneralDegreeFormula.IsIndependenceNumber G alpha)
      (I : Finset (Fin n)) (_ : PalomaMax2SAT.GeneralDegreeFormula.Independent G I)
      (_ : 8 * alpha ≤ ∑ v, (deg v + 1) + m) (_ : 18785 * alpha ≤ 20000 * I.card),
      PalomaMax2SAT.GeneralDegreeFormula.satCount G
          (PalomaMax2SAT.GeneralDegreeFormula.assignmentOfIndependent I) =
        ∑ v, (deg v + 1) + m + I.card ∧
      9932 * (∑ v, (deg v + 1) + m + alpha) ≤
        10000 * PalomaMax2SAT.GeneralDegreeFormula.satCount G
          (PalomaMax2SAT.GeneralDegreeFormula.assignmentOfIndependent I) ∧
      83 * (∑ v, (deg v + 1) + m + alpha) ≤
        84 * PalomaMax2SAT.GeneralDegreeFormula.satCount G
          (PalomaMax2SAT.GeneralDegreeFormula.assignmentOfIndependent I) := by sorry
