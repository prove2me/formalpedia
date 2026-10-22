-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_cumCheck_inv_filter_polytime
-- name    : ProjSchedTW.Complexity.cumCheck_inv_filter_polytime
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:08:44.797715+00:00
-- url     : https://prove2.me/theorems/ee49d5c2-417c-48d5-b2e6-871fc5324297
-- title:
--   Polynomial-time stack-program filter for the inventory constraints of a cumulative-feasibility certificate
-- statement:
--   Checker inputs are words over $\{\bot\}\cup\iota_1(\Sigma)\cup\iota_2(\Sigma)$ ($\Sigma$ = `BSym`) of the form $$u=\iota_1(\mathrm{enc}(c))\,\bot\,\iota_2(\mathrm{enc}(d)),\qquad c\in\mathbb Z^*,\ d\in\mathbb N^*,$$ where $c$ is the integer code of a cumulative instance (`CumInstance.code`: $n$, $m$, durations $p_i$, arc flags and time lags $(a_{ij},\delta_{ij})$, resource rows $r_{ik}$, bounds $\underline R_k,\overline R_k$) and $d=(S_0,\dots,S_{N-1},\mathrm{ord}_0,\dots,\mathrm{ord}_{N-1})$ is the guessed certificate; $N:=\lfloor |d|/2\rfloor$ and entries out of range read as $0$. There is a polynomial-time stack program that outputs the empty word exactly on the inputs $u=\iota_1(\mathrm{enc}(c))\bot\iota_2(\mathrm{enc}(d))$ for which, with $M=\lceil(|c|-(2N^2+N+2))/(N+2)\rceil$ resources, some resource $k<M$ violates $$\underline R_k\le\sum_{i<N}r_{ik}\le\overline R_k\quad\text{or}\quad \underline R_k\le r_k(S,T)\le\overline R_k\ \text{ at an event time } T\in\{S_i,\ S_i+p_i^+\},$$ where $r_k(S,T)=\sum_{j<N}r_{jk}[\,r_{jk}<0\wedge S_j\le T\ \vee\ r_{jk}>0\wedge S_j+p_j^+\le T\,]$ is the inventory of resource $k$ at time $T$; it outputs $u$ on every other input.
--
--   Role: one of five polynomial-time stack-program filters (length/shape, well-formedness, temporal constraints, inventory, acyclic numbering) whose composition decides the checking language of the certificate relation used to place cumulative-resource feasibility in NP.
--
--   **Formalization Note**: the program is a `CookPvsNP.StackProg`; positions are read with `List.getD` (default $0$), and polynomial time is the bound $n\le|u|^k+k$ on the number of execution steps.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, https://doi.org/10.1007/978-3-540-24800-2, p. 130, proof of Theorem 2.12.1, first paragraph (NP membership: a guessed schedule is checked for time- and resource-feasibility in polynomial time)

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

open CookPvsNP

namespace ProjSchedTW.Complexity

theorem cumCheck_inv_filter_polytime : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ N M : ℕ, N = d.length / 2 →
            M = (c.length - (2 * N * N + N + 2) + (N + 2) - 1) / (N + 2) → ∀ k < M,
            (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ∧
              ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ≤
                c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0) ∧
            ∀ i < N, ∀ T : ℕ, (T = d.getD i 0 ∨ T = d.getD i 0 + (c.getD (2 + i) 0).toNat) →
              (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                  ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ∧
                ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ≤
                  c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0))) → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ N M : ℕ, N = d.length / 2 →
            M = (c.length - (2 * N * N + N + 2) + (N + 2) - 1) / (N + 2) → ∀ k < M,
            (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ∧
              ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ≤
                c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0) ∧
            ∀ i < N, ∀ T : ℕ, (T = d.getD i 0 ∨ T = d.getD i 0 + (c.getD (2 + i) 0).toNat) →
              (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                  ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ∧
                ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ≤
                  c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0))) → s ko = u) := by sorry

end ProjSchedTW.Complexity
