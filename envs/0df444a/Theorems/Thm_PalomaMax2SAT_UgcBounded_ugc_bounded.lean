-- Prove2me | Theorems.Thm_PalomaMax2SAT_UgcBounded_ugc_bounded
-- name    : PalomaMax2SAT.UgcBounded.ugc_bounded
-- status  : Proved
-- author  : @vegafrank
-- created : 2026-11-23T06:18:04.908182+00:00
-- url     : https://prove2.me/theorems/3ca93908-150c-4b65-9e9e-94d9884fe07a
-- title:
--   Bounded-degree MAX-CUT and MAX-E2LIN(2): the three-occurrence lift exceeds the Unique Games thresholds ($0.9932>83/84$)
-- statement:
--   The Unique Games Conjecture limits the approximability of $\mathrm{MAX\text{-}2SAT}$ to $\beta^\star\approx 0.94016567$ and of weighted $\mathrm{MAX\text{-}}\{1,2\}\text{-}\mathrm{HORN\text{-}SAT}$ to $\alpha^*\approx 0.94615981$ on general instances. This theorem shows that a graph $G$ of maximum degree $d$ (a $\mathrm{MAX\text{-}CUT}$ or $\mathrm{MAX\text{-}E2LIN}(2)$ instance) can be encoded as a three-occurrence formula $T_{H(G)}$ whose optimum is approximated within a factor above $0.9932>\tfrac{83}{84}$, which exceeds both thresholds.
--
--   The formalized statement says:
--
--   - The thresholds are ordered: $0.94016567<0.94615981<\tfrac{83}{84}<0.9932$.
--   - For a graph $G$ with $m$ edges, every vertex set $S$ selects an independent set of the conflict graph $H(G)$ of size $m+\mathrm{cut}(S)$, and the independence number of $H(G)$ is $m+\mathrm{maxcut}(G)$.
--   - If $G$ has maximum degree at most $d$, then $H(G)$ has maximum degree at most $d+1$, and the degrees of $H(G)$ add up to $4m+2\sum_v\deg(v)^2$, so $H(G)$ has at least $4m$ edges.
--   - An independent set of size $s$ with $18785\,\alpha\le 20000\,s$ lifts to an assignment satisfying at least $0.9932$ (hence at least $\tfrac{83}{84}$) of the optimum of the formula.
--   - For the formula $T_H$ of any port-labelled graph with vertex degrees $d_v$, the optimum is $\sum_v(d_v+1)+m+\alpha$, and the lift of an independent set $I$ satisfies $\sum_v(d_v+1)+m+|I|$ clauses.
--
--   The Goemans--Williamson cut guarantee, the running times, the Unique Games hardness thresholds, and the identification of $T_{H(G)}$ with a port-labelled graph are not formalized.
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
