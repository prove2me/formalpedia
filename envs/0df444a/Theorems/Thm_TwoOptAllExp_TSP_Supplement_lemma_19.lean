-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_lemma_19
-- name    : TwoOptAllExp.TSP.Supplement.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:47:54.217199+00:00
-- url     : https://prove2.me/theorems/30eb2d3e-e173-4c68-8641-f15dda9f2bb7
-- title:
--   Lemma 19 — all following relations of $I_n$ (gadgets, path vertices, boundary), clauses (a)–(f)
-- statement:
--   In the $(2,3,2)$-MCA instance $I_n$ ($n\ge1$) of Section 5:
--
--   1. **(a)** For every $i\in[n]$: $f_1\leftarrow v_{i,2}$, $f_2\leftarrow v_{i,4}$, $g_2\leftarrow v_{i,6}$, $f_3\leftarrow f_1\wedge\bar f_2$, $f_4\leftarrow\bar f_1\wedge f_2$, $f_z\leftarrow f_3\vee f_4$, $g_1\leftarrow f_z$, $g_3\leftarrow g_1\wedge\bar g_2$, $g_4\leftarrow\bar g_1\wedge g_2$, $v_{i-1,1}\leftarrow g_3\vee g_4$ (gadget vertices indexed by $i$); and in every assignment in which none of these ten variables is improving, $$\sigma(v_{i-1,1})=\sigma(v_{i,2})\oplus\sigma(v_{i,4})\oplus\sigma(v_{i,6}).$$
--   2. **(b)** For every $i\in[n]$: $u_1\leftarrow u_0$, $u_2\leftarrow u_1$, $u_3\leftarrow u_2$, $q\leftarrow u_3$; $u_0\leftarrow v_{i-1,8}$ on assignments with $\sigma(v_{i-1,8})=\sigma(u_1)$, and $u_0\leftarrow\bar q$ on assignments with $\sigma(v_{i-1,8})\ne\sigma(u_1)$.
--   3. **(c)** For $1\le i\le n$ and $j\in\{2,4,6\}$: $v_{i,j}\leftarrow v_{i,j-1}$.
--   4. **(d)** For $1\le i\le n$ and $j\in\{3,5,7\}$: $v_{i,j}\leftarrow v_{i,j-1}$ when $\sigma(v_{i,j-1})=\sigma(v_{i,j+1})$; when they differ, $v_{i,3}\leftarrow u_{i,3}$, $v_{i,5}\leftarrow\bar u_{i,2}$, $v_{i,7}\leftarrow u_{i,1}$.
--   5. **(e)** $v_{n,1}\leftarrow\bar v'_1$, $v'_1\leftarrow v'_2$, $v'_2\leftarrow v'_1$, $v_{0,8}\leftarrow v_{0,1}$, and $v'_0$ strictly prefers the value $0$ in every assignment.
--   6. **(f)** For $1\le i<n$: $v_{i,8}\leftarrow v_{i,7}$ if $\sigma(v_{i,7})=\sigma(u_{i+1,0})$, otherwise $v_{i,8}\leftarrow q_i$; for $i=n$ the same with $v'_0$ in place of $u_{n+1,0}$.
--
--   Every relation without a stated restriction holds on all assignments. Together these local facts drive the characterization of all improving flip sequences (Lemmas 24–25).
--
--   Differences from the source:
--   - encoding: x ← φ for a vertex x of I_n → Fol n x φ / FolOn n x φ S: x is a vertex of I_n and follows φ (on S), with values read by val; reason: vertices are named by an inductive type; the named vertex is asserted to exist
--   - encoding: "x when σ(a) = σ(b)" / "otherwise" → FolOn on the sets {σ | val σ a = val σ b} and {σ | val σ a ≠ val σ b}; reason: the source's assignment restrictions
--   - encoding: none of the variables above can be flipped to improve → none of f₁,f₂,g₂,f₃,f₄,f_z,g₁,g₃,g₄,v_{i−1,1} is improving at σ; reason: the ten follower variables listed in (a)
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 19, p. 29 (proof pp. 29–30)

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232

namespace TwoOptAllExp.TSP.Supplement

open MCA232 MCA232.Vx

/-- **Lemma 19** (p. 29). In the instance `I_n` (`n ≥ 1`) of §5.3:
(a) for every `i ∈ [n]`: `f_1 ← v_{i,2}`, `f_2 ← v_{i,4}`, `g_2 ← v_{i,6}`, `f_3 ← f_1 ∧ f̄_2`,
`f_4 ← f̄_1 ∧ f_2`, `f_z ← f_3 ∨ f_4`, `g_1 ← f_z`, `g_3 ← g_1 ∧ ḡ_2`, `g_4 ← ḡ_1 ∧ g_2`,
`v_{i-1,1} ← g_3 ∨ g_4`; and in an assignment in which none of these ten variables is improving,
`σ(v_{i-1,1}) = σ(v_{i,2}) ⊕ σ(v_{i,4}) ⊕ σ(v_{i,6})`;
(b) for every `i ∈ [n]`: `u_1 ← u_0`, `u_2 ← u_1`, `u_3 ← u_2`, `q ← u_3`; `u_0 ← v_{i-1,8}` when
`σ(v_{i-1,8}) = σ(u_1)`, and `u_0 ← q̄` when `σ(v_{i-1,8}) ≠ σ(u_1)`;
(c) for `1 ≤ i ≤ n`, `j ∈ {2, 4, 6}`: `v_{i,j} ← v_{i,j-1}`;
(d) for `1 ≤ i ≤ n`, `j ∈ {3, 5, 7}`: `v_{i,j} ← v_{i,j-1}` when `σ(v_{i,j-1}) = σ(v_{i,j+1})`; when they
differ, `v_{i,3} ← u_{i,3}`, `v_{i,5} ← ū_{i,2}`, `v_{i,7} ← u_{i,1}`;
(e) `v_{n,1} ← v̄′_1`, `v′_1 ← v′_2`, `v′_2 ← v′_1`, `v_{0,8} ← v_{0,1}`, and `v′_0` strictly prefers `0`;
(f) for `1 ≤ i < n`: `v_{i,8} ← v_{i,7}` if `σ(v_{i,7}) = σ(u_{i+1,0})`, otherwise `v_{i,8} ← q_i`; for
`i = n` the same with `v′_0` in place of `u_{n+1,0}`. -/
theorem lemma_19 (n : ℕ) (hn : 1 ≤ n) :
    -- (a)
    (∀ i, 1 ≤ i → i ≤ n →
      Fol n (f1 i) (fun σ => val σ (v i 2)) ∧
      Fol n (f2 i) (fun σ => val σ (v i 4)) ∧
      Fol n (g2 i) (fun σ => val σ (v i 6)) ∧
      Fol n (f3 i) (fun σ => val σ (f1 i) && !val σ (f2 i)) ∧
      Fol n (f4 i) (fun σ => !val σ (f1 i) && val σ (f2 i)) ∧
      Fol n (fz i) (fun σ => val σ (f3 i) || val σ (f4 i)) ∧
      Fol n (g1 i) (fun σ => val σ (fz i)) ∧
      Fol n (g3 i) (fun σ => val σ (g1 i) && !val σ (g2 i)) ∧
      Fol n (g4 i) (fun σ => !val σ (g1 i) && val σ (g2 i)) ∧
      Fol n (v (i - 1) 1) (fun σ => val σ (g3 i) || val σ (g4 i)) ∧
      ∀ σ : V n → Bool,
        (∀ x : V n, x.1 ∈ ({f1 i, f2 i, g2 i, f3 i, f4 i, fz i, g1 i, g3 i, g4 i, v (i - 1) 1} :
          Finset Vx) → ¬ Improving σ x) →
        val σ (v (i - 1) 1) = xor (xor (val σ (v i 2)) (val σ (v i 4))) (val σ (v i 6))) ∧
    -- (b)
    (∀ i, 1 ≤ i → i ≤ n →
      Fol n (u1 i) (fun σ => val σ (u0 i)) ∧
      Fol n (u2 i) (fun σ => val σ (u1 i)) ∧
      Fol n (u3 i) (fun σ => val σ (u2 i)) ∧
      Fol n (q i) (fun σ => val σ (u3 i)) ∧
      FolOn n (u0 i) (fun σ => val σ (v (i - 1) 8)) {σ | val σ (v (i - 1) 8) = val σ (u1 i)} ∧
      FolOn n (u0 i) (fun σ => !val σ (q i)) {σ | val σ (v (i - 1) 8) ≠ val σ (u1 i)}) ∧
    -- (c)
    (∀ i, 1 ≤ i → i ≤ n → ∀ j ∈ ({2, 4, 6} : Finset ℕ),
      Fol n (v i j) (fun σ => val σ (v i (j - 1)))) ∧
    -- (d)
    (∀ i, 1 ≤ i → i ≤ n →
      (∀ j ∈ ({3, 5, 7} : Finset ℕ),
        FolOn n (v i j) (fun σ => val σ (v i (j - 1)))
          {σ | val σ (v i (j - 1)) = val σ (v i (j + 1))}) ∧
      FolOn n (v i 3) (fun σ => val σ (u3 i)) {σ | val σ (v i 2) ≠ val σ (v i 4)} ∧
      FolOn n (v i 5) (fun σ => !val σ (u2 i)) {σ | val σ (v i 4) ≠ val σ (v i 6)} ∧
      FolOn n (v i 7) (fun σ => val σ (u1 i)) {σ | val σ (v i 6) ≠ val σ (v i 8)}) ∧
    -- (e)
    (Fol n (v n 1) (fun σ => !val σ (vp 1)) ∧
      Fol n (vp 1) (fun σ => val σ (vp 2)) ∧
      Fol n (vp 2) (fun σ => val σ (vp 1)) ∧
      Fol n (v 0 8) (fun σ => val σ (v 0 1)) ∧
      Fol n (vp 0) (fun _ => false)) ∧
    -- (f)
    (∀ i, 1 ≤ i → i < n →
      FolOn n (v i 8) (fun σ => val σ (v i 7)) {σ | val σ (v i 7) = val σ (u0 (i + 1))} ∧
      FolOn n (v i 8) (fun σ => val σ (q i)) {σ | val σ (v i 7) ≠ val σ (u0 (i + 1))}) ∧
    (FolOn n (v n 8) (fun σ => val σ (v n 7)) {σ | val σ (v n 7) = val σ (vp 0)} ∧
      FolOn n (v n 8) (fun σ => val σ (q n)) {σ | val σ (v n 7) ≠ val σ (vp 0)}) := by sorry

end TwoOptAllExp.TSP.Supplement
