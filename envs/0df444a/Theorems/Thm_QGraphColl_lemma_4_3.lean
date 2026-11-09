-- Prove2me | Theorems.Thm_QGraphColl_lemma_4_3
-- name    : QGraphColl.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:25.386386+00:00
-- url     : https://prove2.me/theorems/f8d4d2c1-ca4e-4b1f-99b2-9d156a1ab4ab
-- title:
--   Lemma 4.3 — separate thresholds: $\mathrm{vol}(G[P],x)\le a\tau_A+b\tau_B+4\sqrt{abp\eta}$
-- statement:
--   Let $G$ be bipartite with sides $A,B$ of sizes $a,b$ and degrees at most $d_A$ on $A$ and $d_B$ on $B$, and let $x$ be an input with $|M\cap A|\le ap$ and $|M\cap B|\le bp$. Let $z\in\mathbb R^V$ satisfy $\|z-C\mathbf 1_M\|_\infty\le\eta$, where $(C\mathbf 1_M)_v=\sum_w c_{vw}x_w$ and $C=C_A\oplus C_B$ is the same-side common-neighbour matrix. Let $S$ minimize $\psi_z(S)$ over the sets with $|S\cap A|\le ap$ and $|S\cap B|\le bp$, let $\tau_A,\tau_B>0$, and
--   $$P=\{u\in A:\ \ell_u(S)\le\tau_A\}\cup\{u\in B:\ \ell_u(S)\le\tau_B\}.$$
--   Then
--   $$\mathrm{vol}(G[P],x)\le a\tau_A+b\tau_B+4\sqrt{abp\eta},$$
--   and on a negative input the outside cover $V\setminus P$ of the edges outside $G[P]$ has marked volume at most
--   $$4p\eta\left(\frac{d_Ab}{\tau_A^2}+\frac{d_Ba}{\tau_B^2}\right).$$
--
--   This is the thresholding step of the improved algorithm, with a separate threshold on each side.
--
--   Differences from the source:
--   - encoding: C1_M with C = C_A ⊕ C_B → (C1_M)_v = ∑_w c_vw x_w over all w; reason: in a bipartite graph vertices on different sides have no common neighbour, so the off-block entries vanish; same vector
--   - reading: S minimizes ψ_z(S) over subsets satisfying |S ∩ A| ≤ ap and |S ∩ B| ≤ bp → S is feasible and ψ_z(S) ≤ ψ_z(S') for every feasible S'; reason: the meaning of a minimizer
--   - encoding: thresholds τ_A, τ_B (dividing in the cover bound) → τ_A > 0 and τ_B > 0; reason: the bound is undefined at τ = 0; Algorithm 9 supplies τ_A, τ_B > 0
--   - encoding: the outside cover has marked volume at most … → IsCover (G \ restrict G P) (V \ P) and vol(G \ restrict G P, V \ P, x) ≤ …; reason: the outside cover is V \ P for the edges outside G[P] (Algorithm 9 line 6); its marked volume is Definition 2.1 for those edges
--   - generalization: G bipartite with vertex sets A and B (V(G) = A ∪ B) → IsSides G A B on a vertex type that may contain further labels outside A ∪ B; reason: labels outside A ∪ B are isolated; taking V = A ∪ B gives the source's statement
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 4.3, p.24 (C = C_A ⊕ C_B, p.23)

import Mathlib
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol
import Definitions.Def_QGraphColl_restrict

namespace QGraphColl

/-- **Lemma 4.3** (Separate thresholds; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.24). Let `G` be a bipartite graph with `m`
edges, with vertex sets `A` and `B` on both sides of the bipartition, sizes `a` and `b`, degree
upper bounds `d_A` and `d_B`, and such that `|M ∩ A| ≤ ap` and `|M ∩ B| ≤ bp`. Suppose that
`‖z − C1_M‖_∞ ≤ η`. Let `S` minimize `ψ_z(S)` over subsets satisfying `|S ∩ A| ≤ ap` and
`|S ∩ B| ≤ bp`. Define `P = {u ∈ A : ℓ_u(S) ≤ τ_A} ∪ {u ∈ B : ℓ_u(S) ≤ τ_B}`. Then
`vol(G[P], x) ≤ aτ_A + bτ_B + 4√(abpη)`. On a negative input, the outside cover has marked volume
at most `4pη(d_A b/τ_A² + d_B a/τ_B²)`.

**Formalization Note.**
* `C = C_A ⊕ C_B` (p.23) is the same-side common-neighbour matrix. In a bipartite graph two
  vertices on different sides have no common neighbour, so `(C1_M)_v = ∑_w c_vw x_w` over all `w`.
* "`S` minimizes `ψ_z`": `S` is feasible and `ψ_z(S) ≤ ψ_z(S')` for every feasible `S' ⊆ V`.
* The outside cover is `V \ P`, for the edges `G \ G[P]` outside `G[P]`; its marked volume uses
  degrees in that edge set. The cover property is stated with it.
* `τ_A, τ_B > 0` (they divide). The edge count `m` does not enter the conclusion. Labels outside
  `A ∪ B` are allowed; they are isolated. -/
theorem lemma_4_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    (hAB : IsSides G A B) (dA dB : ℝ) (hdA : ∀ v ∈ A, (deg G v : ℝ) ≤ dA)
    (hdB : ∀ v ∈ B, (deg G v : ℝ) ≤ dB) (x : V → Bool) (p : ℝ)
    (hMA : ((marked x ∩ A).card : ℝ) ≤ A.card * p) (hMB : ((marked x ∩ B).card : ℝ) ≤ B.card * p)
    (z : V → ℝ) (η : ℝ)
    (hz : ∀ v, |z v - ∑ w, (cn G v w : ℝ) * (if x w = true then 1 else 0)| ≤ η)
    (S : Finset V) (hSA : ((S ∩ A).card : ℝ) ≤ A.card * p) (hSB : ((S ∩ B).card : ℝ) ≤ B.card * p)
    (hmin : ∀ S' : Finset V, ((S' ∩ A).card : ℝ) ≤ A.card * p →
      ((S' ∩ B).card : ℝ) ≤ B.card * p → psi G z S ≤ psi G z S')
    (τA τB : ℝ) (hτA : 0 < τA) (hτB : 0 < τB) :
    let P : Finset V := A.filter (fun u => (ell G S u : ℝ) ≤ τA) ∪
      B.filter (fun u => (ell G S u : ℝ) ≤ τB)
    (vol (restrict G P) Finset.univ x : ℝ) ≤
        A.card * τA + B.card * τB + 4 * Real.sqrt (A.card * B.card * p * η) ∧
      (gc G x = false →
        IsCover (G \ restrict G P) (Finset.univ \ P) ∧
        (vol (G \ restrict G P) (Finset.univ \ P) x : ℝ) ≤
          4 * p * η * (dA * B.card / τA ^ 2 + dB * A.card / τB ^ 2)) := by sorry

end QGraphColl
