-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_cumCheck_wf_filter_polytime
-- name    : ProjSchedTW.Complexity.cumCheck_wf_filter_polytime
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:07:39.302916+00:00
-- url     : https://prove2.me/theorems/17640783-3529-4da5-a5c3-3b94a48d0fb7
-- title:
--   Polynomial-time stack-program filter for the well-formedness token conditions of a cumulative-feasibility certificate
-- statement:
--   Checker inputs are words over $\{\bot\}\cup\iota_1(\Sigma)\cup\iota_2(\Sigma)$ ($\Sigma$ = `BSym`) of the form $$u=\iota_1(\mathrm{enc}(c))\,\bot\,\iota_2(\mathrm{enc}(d)),\qquad c\in\mathbb Z^*,\ d\in\mathbb N^*,$$ where $c$ is the integer code of a cumulative instance (`CumInstance.code`: $n$, $m$, durations $p_i$, arc flags and time lags $(a_{ij},\delta_{ij})$, resource rows $r_{ik}$, bounds $\underline R_k,\overline R_k$) and $d=(S_0,\dots,S_{N-1},\mathrm{ord}_0,\dots,\mathrm{ord}_{N-1})$ is the guessed certificate; $N:=\lfloor |d|/2\rfloor$ and entries out of range read as $0$. There is a polynomial-time stack program that outputs the empty word exactly on the inputs $u=\iota_1(\mathrm{enc}(c))\bot\iota_2(\mathrm{enc}(d))$ violating $$p_i\ge 0\ (i<N),\quad p_0=p_{N-1}=0,\quad a_{ij}\in\{0,1\}\ (i,j<N),\quad a_{ii}=0,$$ where $p_i=c_{2+i}$ and $a_{ij}=c_{2+N+2(iN+j)}$, and outputs $u$ on every other input.
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

theorem cumCheck_wf_filter_polytime : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬((∀ i < d.length / 2, 0 ≤ c.getD (2 + i) 0) ∧
            (c.getD 2 0 = 0 ∧ c.getD (2 + (d.length / 2 - 1)) 0 = 0) ∧
            (∀ q < d.length / 2 * (d.length / 2), c.getD (2 + d.length / 2 + 2 * q) 0 = 0 ∨
              c.getD (2 + d.length / 2 + 2 * q) 0 = 1) ∧
            (∀ i < d.length / 2, c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + i)) 0 = 0)))
        → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬((∀ i < d.length / 2, 0 ≤ c.getD (2 + i) 0) ∧
            (c.getD 2 0 = 0 ∧ c.getD (2 + (d.length / 2 - 1)) 0 = 0) ∧
            (∀ q < d.length / 2 * (d.length / 2), c.getD (2 + d.length / 2 + 2 * q) 0 = 0 ∨
              c.getD (2 + d.length / 2 + 2 * q) 0 = 1) ∧
            (∀ i < d.length / 2, c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + i)) 0 = 0)))
        → s ko = u) := by sorry

end ProjSchedTW.Complexity
