-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_cumCheck_len_filter_polytime
-- name    : ProjSchedTW.Complexity.cumCheck_len_filter_polytime
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:07:07.313791+00:00
-- url     : https://prove2.me/theorems/d2b46d48-8792-4abb-93e8-09cacbdd4ccc
-- title:
--   Polynomial-time stack-program filter for the shape and lengths of a cumulative-feasibility certificate
-- statement:
--   Checker inputs are words over $\{\bot\}\cup\iota_1(\Sigma)\cup\iota_2(\Sigma)$ ($\Sigma$ = `BSym`) of the form $$u=\iota_1(\mathrm{enc}(c))\,\bot\,\iota_2(\mathrm{enc}(d)),\qquad c\in\mathbb Z^*,\ d\in\mathbb N^*,$$ where $c$ is the integer code of a cumulative instance (`CumInstance.code`: $n$, $m$, durations $p_i$, arc flags and time lags $(a_{ij},\delta_{ij})$, resource rows $r_{ik}$, bounds $\underline R_k,\overline R_k$) and $d=(S_0,\dots,S_{N-1},\mathrm{ord}_0,\dots,\mathrm{ord}_{N-1})$ is the guessed certificate; $N:=\lfloor |d|/2\rfloor$ and entries out of range read as $0$. There is a stack program $p$ with input stack $k_i$ and output stack $k_o$ that halts within $|u|^k+k$ steps on every input $u$ and leaves on $k_o$ the word $u$ itself when $u$ has the form above with $c_0\ge 1$, $c_1\ge 0$, $$|c|=2+(n+2)+2(n+2)^2+(n+2)m+2m,\qquad |d|=2(n+2)\qquad(n=c_0,\ m=c_1),$$ and the empty word otherwise.
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

theorem cumCheck_len_filter_polytime : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          1 ≤ c.getD 0 0 ∧ 0 ≤ c.getD 1 0 ∧
          c.length = 2 + ((c.getD 0 0).toNat + 2) +
            2 * (((c.getD 0 0).toNat + 2) * ((c.getD 0 0).toNat + 2)) +
            ((c.getD 0 0).toNat + 2) * (c.getD 1 0).toNat + (c.getD 1 0).toNat +
            (c.getD 1 0).toNat ∧
          d.length = 2 * ((c.getD 0 0).toNat + 2)) → s ko = u) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          1 ≤ c.getD 0 0 ∧ 0 ≤ c.getD 1 0 ∧
          c.length = 2 + ((c.getD 0 0).toNat + 2) +
            2 * (((c.getD 0 0).toNat + 2) * ((c.getD 0 0).toNat + 2)) +
            ((c.getD 0 0).toNat + 2) * (c.getD 1 0).toNat + (c.getD 1 0).toNat +
            (c.getD 1 0).toNat ∧
          d.length = 2 * ((c.getD 0 0).toNat + 2)) → s ko = []) := by sorry

end ProjSchedTW.Complexity
