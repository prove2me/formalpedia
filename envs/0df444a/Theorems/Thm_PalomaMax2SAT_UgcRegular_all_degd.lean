-- Prove2me | Theorems.Thm_PalomaMax2SAT_UgcRegular_all_degd
-- name    : PalomaMax2SAT.UgcRegular.all_degd
-- status  : Proved
-- author  : @vegafrank
-- created : 2026-11-23T08:46:56.554375+00:00
-- url     : https://prove2.me/theorems/0e9bbdb8-656d-40f9-ade9-3d9064d4bb23
-- title:
--   Complete classification of the three-occurrence Horn formulas of $d$-regular graphs for all $d\ge1$
-- statement:
--   Let $H$ be a simple $d$-regular graph with $n$ vertices and $m=dn/2$ edges, with a port labelling, and let $T_H$ be the three-occurrence Horn formula with $d+1$ clones at every vertex. (1) For $d\ge1$, the maximum number of satisfied clauses is $(d+1)n+m+\alpha(H)$, $2m=dn$ and $2\alpha(H)\le n$. (2) Every assignment $z$ is repaired to an independent set $R(z)$ with $\mathrm{score}(z)\le(d+1)n+m+|R(z)|$. (3) The assignment of an independent set $I$ (clones of vertices of $I$ false, all others true) satisfies exactly $(d+1)n+m+|I|$ clauses. (4) The all-true assignment satisfies at least $\frac{3d+2}{3d+3}$ of the optimum for every $d\ge1$, and at least $\frac{83}{84}$ for $d\ge27$. (5) If $6\alpha\le7|I|$ the lift of $I$ satisfies at least $\frac{21d+20}{21d+21}$ of the optimum, for every $d\ge1$. (6) If $27\alpha\le28|I|+d\alpha$ the lift satisfies at least $\frac{83}{84}$ of the optimum, for every $d\ge1$. (7) If $d\ge22$ and $5\alpha\le(d+3)|I|$ the lift satisfies at least $\frac{83}{84}$ of the optimum; for every degree $e+2$ and $\varepsilon=1/c$ the division-free form of the ratio $1-\frac{d-2+\varepsilon}{(3d+3)(d+3+\varepsilon)}$ holds. (8) For $d=21$, an independent set satisfying $50\alpha\le241|I|$ when $200\alpha\le99n$ and $3n\le25|I|$ when $99n<200\alpha$ has a lift of ratio at least $\frac{83}{84}$. (9) For $d=1$, $\alpha(H)=m=n/2$ and the optimum is $3n$; for $d=2$, $m=n$ and the optimum is $4n+\alpha(H)$. The polynomial running times, the exact computation of a maximum independent set on paths and cycles, and the Berman--Fujito, Trevisan and Goemans--Williamson guarantees are not formalized.
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
