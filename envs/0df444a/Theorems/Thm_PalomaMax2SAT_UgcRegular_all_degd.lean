-- Prove2me | Theorems.Thm_PalomaMax2SAT_UgcRegular_all_degd
-- name    : PalomaMax2SAT.UgcRegular.all_degd
-- status  : Proved
-- author  : @vegafrank
-- created : 2026-11-23T08:46:56.554375+00:00
-- url     : https://prove2.me/theorems/0e9bbdb8-656d-40f9-ade9-3d9064d4bb23
-- title:
--   Three-occurrence Horn formulas of $d$-regular graphs: exact optimum and approximation ratios for every $d\ge 1$
-- statement:
--   A $d$-regular graph $H$ with $n$ vertices and $m=dn/2$ edges is turned into a three-occurrence Horn formula $T_H$ by replacing every vertex with $d+1$ clones. This theorem determines the optimum of $T_H$ exactly in terms of the independence number $\alpha(H)$, and gives approximation ratios for it from independent sets of $H$, for every degree $d\ge 1$.
--
--   The formalized statement says:
--
--   - The maximum number of satisfied clauses of $T_H$ is $(d+1)n+m+\alpha(H)$, and $2\alpha(H)\le n$.
--   - Every assignment can be repaired to an independent set $R$ whose value is at least the score of the assignment, and an independent set $I$ gives an assignment satisfying exactly $(d+1)n+m+|I|$ clauses.
--   - The all-true assignment satisfies at least $\tfrac{3d+2}{3d+3}$ of the optimum for every $d\ge1$, and at least $\tfrac{83}{84}$ for $d\ge27$.
--   - If $6\alpha\le 7|I|$, the lift of $I$ satisfies at least $\tfrac{21d+20}{21d+21}$ of the optimum for every $d\ge1$.
--   - If $27\alpha\le 28|I|+d\alpha$, the lift satisfies at least $\tfrac{83}{84}$ of the optimum for every $d\ge1$. The same holds for $d\ge 22$ when $5\alpha\le (d+3)|I|$ and for $d=21$ under a two-case condition on $|I|$.
--   - For $d=1$ the independence number is $m=n/2$ and the optimum is $3n$; for $d=2$ the optimum is $4n+\alpha(H)$.
--
--   The polynomial running times, the exact computation of a maximum independent set on paths and cycles, and the Berman--Fujito, Trevisan and Goemans--Williamson guarantees are not formalized.
-- source:
--   https://github.com/frankvegadelgado/paloma/blob/afdff6eea63634613b0adda9cb2526f3c96af8b6/doc/paper.tex#L203

import Mathlib
import Definitions.Def_PalomaMax2SAT_UgcRegular_Defs

theorem PalomaMax2SAT.UgcRegular.all_degd :
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 0 < d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G))
            ((d + 1) * n + m + alpha) ∧
          2 * m = d * n ∧ 2 * alpha ≤ n) ∧
    (∀ {d n m : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m)
        (z : Fin n → Fin (d + 1) → Bool),
      PalomaMax2SAT.DegreeFormula.Independent G
          (PalomaMax2SAT.DegreeFormula.repairedSet G z) ∧
        PalomaMax2SAT.DegreeFormula.score G z ≤
          (d + 1) * n + m + (PalomaMax2SAT.DegreeFormula.repairedSet G z).card) ∧
    (∀ {d n m : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m) (I : Finset (Fin n)),
      PalomaMax2SAT.DegreeFormula.Independent G I →
        PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
              Fin n → Fin (d + 1) → Bool) = (d + 1) * n + m + I.card) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 0 < d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        (3 * d + 2) * ((d + 1) * n + m + alpha) ≤
          (3 * d + 3) * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent (∅ : Finset (Fin n)) :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 27 ≤ d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        83 * ((d + 1) * n + m + alpha) ≤
          84 * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent (∅ : Finset (Fin n)) :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 0 < d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I → 6 * alpha ≤ 7 * I.card →
        (21 * d + 20) * ((d + 1) * n + m + alpha) ≤
          (21 * d + 21) * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 0 < d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I → 27 * alpha ≤ 28 * I.card + d * alpha →
        83 * ((d + 1) * n + m + alpha) ≤
          84 * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {d n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph d n m), 22 ≤ d →
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I → 5 * alpha ≤ (d + 3) * I.card →
        83 * ((d + 1) * n + m + alpha) ≤
          84 * PalomaMax2SAT.DegreeFormula.satCount G
            (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
              Fin n → Fin (d + 1) → Bool)) ∧
    (∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 21 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I →
        (200 * alpha ≤ 99 * n → 50 * alpha ≤ 241 * I.card) →
        (99 * n < 200 * alpha → 3 * n ≤ 25 * I.card) →
          83 * ((21 + 1) * n + m + alpha) ≤
            84 * PalomaMax2SAT.DegreeFormula.satCount G
              (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
                Fin n → Fin (21 + 1) → Bool)) ∧
    (∀ {e n m alpha c : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph (e + 2) n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha → ∀ I : Finset (Fin n),
      PalomaMax2SAT.DegreeFormula.Independent G I →
        5 * c * alpha ≤ (((e + 2) + 3) * c + 1) * I.card →
          (3 * (e + 2) + 3) * (((e + 2) + 3) * c + 1) * ((e + 2 + 1) * n + m + alpha) ≤
            (3 * (e + 2) + 3) * (((e + 2) + 3) * c + 1) *
                PalomaMax2SAT.DegreeFormula.satCount G
                  (PalomaMax2SAT.DegreeFormula.assignmentOfIndependent I :
                    Fin n → Fin (e + 2 + 1) → Bool) +
              (e * c + 1) * ((e + 2 + 1) * n + m + alpha)) ∧
    (∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 1 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        alpha = m ∧
          IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G)) (3 * n)) ∧
    (∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 2 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        m = n ∧
          IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G)) (4 * n + alpha)) := by sorry
