-- Prove2me | Theorems.Thm_PhaseEncodedQGE_Supplement_theorem_A_16
-- name    : PhaseEncodedQGE.Supplement.theorem_A_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:32:03.225021+00:00
-- url     : https://prove2.me/theorems/e0507c9a-4fc4-434f-a795-72a06c2b0483
-- title:
--   Theorem A.16 (= 4.3) — two- and three-defect histograms at girth $\ge5$ as functions of $(n,C_5,C_6)$
-- statement:
--   Let $G$ be a simple cubic graph on $n$ vertices with girth $g\ge5$, and write $C_5$, $C_6$ for its numbers of five- and six-cycles. For a defect set $D$, $E_{\mathrm{in}}(D)=q^{\mathrm{in}}_0+q^{\mathrm{in}}_3$ and $E_{\mathrm{out}}(D)=q^{\mathrm{out}}_0+q^{\mathrm{out}}_3$ are its extremal counts and $(q_3-q_0,q_2-q_1)^{\mathrm{in}}$, $(q_3-q_0,q_2-q_1)^{\mathrm{out}}$ its odd readings.
--
--   1. The two-defect histogram of $(E_{\mathrm{in}},E_{\mathrm{out}})$ has the entries $(0,n-6)$ with multiplicity $3n/2$, $(2,n-7)$ with multiplicity $3n$, and $(2,n-8)$ with multiplicity $\binom n2-9n/2$.
--   2. The three-defect histogram of $(E_{\mathrm{in}},E_{\mathrm{out}})$ is Table 1:
--
--   | entry | multiplicity | entry | multiplicity |
--   |---|---|---|---|
--   | $(0,n-8)$ | $3n$ | $(3,n-12)$ | $\binom n3-\frac92n^2+41n-5C_5-2C_6$ |
--   | $(1,n-10)$ | $\frac32n(n-14)+5C_5$ | $(3,n-11)$ | $3n^2-48n+10C_5+6C_6$ |
--   | $(1,n-9)$ | $12n-10C_5$ | $(3,n-10)$ | $12n-5C_5-6C_6$ |
--   | $(1,n-8)$ | $5C_5$ | $(3,n-9)$ | $n+2C_6$ |
--
--   3. The odd-reading histogram of the three-defect layer is a function of $(n,C_5,C_6)$: the three-sets with two internal edges (inside reading $(0,-1)$) all have outside readings $(-(n-8),-5)$; those with one internal edge (inside reading $(-1,-2)$) and outside readings $(-(n-10)-w,\,3w-7)$ number $m_w$, the $(1,n-10+w)$ entry of Table 1, for $w=0,1,2$; and the independent three-sets (inside reading $(-3,0)$) with outside readings $(-(n-12)-w,\,3w-9)$ number $n_0$, $n_1+n$, $n_2$ and $2C_6$ for $w=0,1,2,3$, where $n_w$ is the $(3,n-12+w)$ entry of the table.
--   4. Consequently the two-defect histogram depends on $n$ alone; the three-defect histograms of the extremal counts and of the odd readings are functions of $(n,C_5,C_6)$ and each determines $C_5$ and $C_6$; and at $g\ge7$ both depend on $n$ alone.
--
--   In particular $5C_5$ three-sets have one internal edge and outside readings $(-(n-8),-1)$, and $2C_6$ independent three-sets have outside readings $(-(n-9),0)$. Combined with the layer-determination theorems, the first three layers of the sorted readout determine $C_5$, $C_6$ and the girth up to seven.
--
--   **Formalization Note** Girth is Mathlib's `SimpleGraph.girth` in $\mathbb N_\infty$; $C_5$, $C_6$ are subgraph cycle counts. The extremal histogram is cast injectively to integer keys so that keys such as $n-12$ are not truncated, and multiplicities are compared as rational numbers. "Depends on", "function of" and "determines" compare two such graphs on the same vertex set.
--
--   Differences from the source:
--   - encoding: multiplicities $3n/2$, $\binom n2-9n/2$, $\frac32n(n-14)$, … and entries such as $(3,n-12)$ → counts of the histogram (cast to integer keys) compared in $\mathbb Q$; reason: avoids truncated natural-number subtraction and division; the same numbers on every instance
--   - encoding: "has the entries" / "is the one in Table 1" / "all have outside readings" → each listed key has the stated multiplicity and every other key multiplicity $0$; reason: that is what equality of a histogram with a listed table means
--   - encoding: (c) counts of three-sets with $e$ internal edges and given outside readings → counts of keys (inside reading, outside reading) of the full odd-reading histogram, with the inside reading $(0,-1)$, $(-1,-2)$, $(-3,0)$ for $e=2,1,0$; reason: by (37) the inside reading of a three-set determines e, so the two counts coincide; the number 3n of three-sets with two internal edges is the e = 2 entry of Table 1
--   - reading: "depends on $n$ alone" / "are functions of $(n,C_5,C_6)$" / "each determines $C_5$ and $C_6$" → for every second cubic graph $H$ of girth $\ge5$ on the same vertex set: equal histograms (resp. equal $C_5,C_6$ ⇒ equal histograms; equal histogram ⇒ equal $C_5,C_6$); reason: a quantity is a function of (or determines) another exactly when equality of the one forces equality of the other, compared between graphs of the same order
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.5, pp.18–19 (PDF pp.19–20), Theorem A.16 (= Theorem 4.3, p.8 (PDF p.9)) and Table 1, p.9 (PDF p.10); inside readings from Proposition A.14, eq. (37), p.17 (PDF p.18)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Profile
import Definitions.Def_PhaseEncodedQGE_Supplement_GraphCounts
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

/-- Theorem A.16 (= Theorem 4.3), three defects at girth at least five (Miller, Lee, *Structural
Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03),
App. A.1.5, pp.18–19; body twin Theorem 4.3, p.8, with Table 1, p.9).

Let `G` be a simple cubic graph on `n` vertices with girth `g ≥ 5`.
(a) The two-defect histogram of `(E_in, E_out)` has the entries `(0, n − 6)` with multiplicity
`3n/2`, `(2, n − 7)` with multiplicity `3n` and `(2, n − 8)` with multiplicity `(n choose 2) − 9n/2`.
(b) The three-defect histogram of `(E_in, E_out)` is Table 1: `(0, n−8)`: `3n`; `(1, n−10)`:
`(3/2)n(n−14) + 5C₅`; `(1, n−9)`: `12n − 10C₅`; `(1, n−8)`: `5C₅`; `(3, n−12)`:
`(n choose 3) − (9/2)n² + 41n − 5C₅ − 2C₆`; `(3, n−11)`: `3n² − 48n + 10C₅ + 6C₆`; `(3, n−10)`:
`12n − 5C₅ − 6C₆`; `(3, n−9)`: `n + 2C₆`.
(c) The odd-reading histogram of the three-defect layer: the three-sets with two internal edges
(inside reading `(0, −1)`) all have outside readings `(−(n − 8), −5)`; those with one internal edge
(inside reading `(−1, −2)`) and outside readings `(−(n − 10) − w, 3w − 7)` number `m_w`, the
`(1, n − 10 + w)` entry of Table 1, `w = 0, 1, 2`; the independent three-sets (inside reading
`(−3, 0)`) with outside readings `(−(n − 12) − w, 3w − 9)` number `n₀`, `n₁ + n`, `n₂`, `2C₆` for
`w = 0, 1, 2, 3`, where `n_w` is the `(3, n − 12 + w)` entry of the table.
Consequently the two-defect histogram depends on `n` alone; the three-defect histograms of the
extremal counts and of the odd readings are functions of `(n, C₅, C₆)` and each determines `C₅`
and `C₆`; and at `g ≥ 7` both depend on `n` alone.

**Formalization Note** `g ≥ 5` is `(5 : ℕ∞) ≤ G.girth` (Mathlib's girth, `⊤` for an acyclic
graph). `C₅`, `C₆` are subgraph cycle counts (`cycleCount`). The histograms are the base
multisets `extremalHist` (keys in `ℕ × ℕ`, cast injectively to `ℤ × ℤ` so that keys such as
`n − 12` are not truncated) and `oddHist` (keys `(inside reading, outside reading)`); the inside
reading of a three-set is fixed by its number `e` of internal edges, by (37), p.17. Multiplicities
are compared in `ℚ`, so `3n/2`, `(3/2)n(n−14)`, `(9/2)n²` and the binomials involve no truncated
`ℕ` arithmetic. "Has the entries" / "is the one in Table 1" / "number": each listed key has the
stated multiplicity and every other key has multiplicity `0`. "Depends on `n` alone",
"function of `(n, C₅, C₆)`" and "determines" compare two such graphs on the same vertex set. -/
theorem theorem_A_16 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → (5 : ℕ∞) ≤ G.girth →
      -- (a) the two-defect histogram of (E_in, E_out)
      ((((extremalHist G 2).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (0, (n : ℤ) - 6) : ℚ) =
          3 * (n : ℚ) / 2 ∧
        (((extremalHist G 2).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (2, (n : ℤ) - 7) : ℚ) =
          3 * (n : ℚ) ∧
        (((extremalHist G 2).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (2, (n : ℤ) - 8) : ℚ) =
          ((n.choose 2 : ℕ) : ℚ) - 9 * (n : ℚ) / 2 ∧
        ∀ p : ℤ × ℤ, p ≠ (0, (n : ℤ) - 6) → p ≠ (2, (n : ℤ) - 7) → p ≠ (2, (n : ℤ) - 8) →
          ((extremalHist G 2).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count p = 0) ∧
      -- (b) the three-defect histogram of (E_in, E_out): Table 1
      ((((extremalHist G 3).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (0, (n : ℤ) - 8) : ℚ) =
          3 * (n : ℚ) ∧
        (((extremalHist G 3).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (1, (n : ℤ) - 10) : ℚ) =
          3 / 2 * (n : ℚ) * ((n : ℚ) - 14) + 5 * (cycleCount G 5 : ℚ) ∧
        (((extremalHist G 3).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (1, (n : ℤ) - 9) : ℚ) =
          12 * (n : ℚ) - 10 * (cycleCount G 5 : ℚ) ∧
        (((extremalHist G 3).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (1, (n : ℤ) - 8) : ℚ) =
          5 * (cycleCount G 5 : ℚ) ∧
        (((extremalHist G 3).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (3, (n : ℤ) - 12) : ℚ) =
          ((n.choose 3 : ℕ) : ℚ) - 9 / 2 * (n : ℚ) ^ 2 + 41 * (n : ℚ) -
            5 * (cycleCount G 5 : ℚ) - 2 * (cycleCount G 6 : ℚ) ∧
        (((extremalHist G 3).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (3, (n : ℤ) - 11) : ℚ) =
          3 * (n : ℚ) ^ 2 - 48 * (n : ℚ) + 10 * (cycleCount G 5 : ℚ) +
            6 * (cycleCount G 6 : ℚ) ∧
        (((extremalHist G 3).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (3, (n : ℤ) - 10) : ℚ) =
          12 * (n : ℚ) - 5 * (cycleCount G 5 : ℚ) - 6 * (cycleCount G 6 : ℚ) ∧
        (((extremalHist G 3).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count (3, (n : ℤ) - 9) : ℚ) =
          (n : ℚ) + 2 * (cycleCount G 6 : ℚ) ∧
        ∀ p : ℤ × ℤ, p ≠ (0, (n : ℤ) - 8) → p ≠ (1, (n : ℤ) - 10) → p ≠ (1, (n : ℤ) - 9) →
          p ≠ (1, (n : ℤ) - 8) → p ≠ (3, (n : ℤ) - 12) → p ≠ (3, (n : ℤ) - 11) →
          p ≠ (3, (n : ℤ) - 10) → p ≠ (3, (n : ℤ) - 9) →
          ((extremalHist G 3).map (fun p => ((p.1 : ℤ), (p.2 : ℤ)))).count p = 0) ∧
      -- (c) the odd-reading histogram of the three-defect layer
      (((oddHist G 3).count ((0, -1), (-((n : ℤ) - 8), -5)) : ℚ) = 3 * (n : ℚ) ∧
        ((oddHist G 3).count ((-1, -2), (-((n : ℤ) - 10) - 0, 3 * 0 - 7)) : ℚ) =
          3 / 2 * (n : ℚ) * ((n : ℚ) - 14) + 5 * (cycleCount G 5 : ℚ) ∧
        ((oddHist G 3).count ((-1, -2), (-((n : ℤ) - 10) - 1, 3 * 1 - 7)) : ℚ) =
          12 * (n : ℚ) - 10 * (cycleCount G 5 : ℚ) ∧
        ((oddHist G 3).count ((-1, -2), (-((n : ℤ) - 10) - 2, 3 * 2 - 7)) : ℚ) =
          5 * (cycleCount G 5 : ℚ) ∧
        ((oddHist G 3).count ((-3, 0), (-((n : ℤ) - 12) - 0, 3 * 0 - 9)) : ℚ) =
          ((n.choose 3 : ℕ) : ℚ) - 9 / 2 * (n : ℚ) ^ 2 + 41 * (n : ℚ) -
            5 * (cycleCount G 5 : ℚ) - 2 * (cycleCount G 6 : ℚ) ∧
        ((oddHist G 3).count ((-3, 0), (-((n : ℤ) - 12) - 1, 3 * 1 - 9)) : ℚ) =
          (3 * (n : ℚ) ^ 2 - 48 * (n : ℚ) + 10 * (cycleCount G 5 : ℚ) +
            6 * (cycleCount G 6 : ℚ)) + (n : ℚ) ∧
        ((oddHist G 3).count ((-3, 0), (-((n : ℤ) - 12) - 2, 3 * 2 - 9)) : ℚ) =
          12 * (n : ℚ) - 5 * (cycleCount G 5 : ℚ) - 6 * (cycleCount G 6 : ℚ) ∧
        ((oddHist G 3).count ((-3, 0), (-((n : ℤ) - 12) - 3, 3 * 3 - 9)) : ℚ) =
          2 * (cycleCount G 6 : ℚ) ∧
        ∀ p : (ℤ × ℤ) × (ℤ × ℤ), p ≠ ((0, -1), (-((n : ℤ) - 8), -5)) →
          (∀ w : ℤ, 0 ≤ w → w ≤ 2 → p ≠ ((-1, -2), (-((n : ℤ) - 10) - w, 3 * w - 7))) →
          (∀ w : ℤ, 0 ≤ w → w ≤ 3 → p ≠ ((-3, 0), (-((n : ℤ) - 12) - w, 3 * w - 9))) →
          (oddHist G 3).count p = 0) ∧
      -- Consequently
      (∀ H : SimpleGraph (Fin n), IsCubic H → (5 : ℕ∞) ≤ H.girth →
        extremalHist G 2 = extremalHist H 2 ∧
        (cycleCount G 5 = cycleCount H 5 → cycleCount G 6 = cycleCount H 6 →
          extremalHist G 3 = extremalHist H 3 ∧ oddHist G 3 = oddHist H 3) ∧
        (extremalHist G 3 = extremalHist H 3 →
          cycleCount G 5 = cycleCount H 5 ∧ cycleCount G 6 = cycleCount H 6) ∧
        (oddHist G 3 = oddHist H 3 →
          cycleCount G 5 = cycleCount H 5 ∧ cycleCount G 6 = cycleCount H 6) ∧
        ((7 : ℕ∞) ≤ G.girth → (7 : ℕ∞) ≤ H.girth →
          extremalHist G 3 = extremalHist H 3 ∧ oddHist G 3 = oddHist H 3)) := by sorry

end PhaseEncodedQGE.Supplement
