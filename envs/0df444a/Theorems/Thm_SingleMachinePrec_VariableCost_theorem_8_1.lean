-- Prove2me | Theorems.Thm_SingleMachinePrec_VariableCost_theorem_8_1
-- name    : SingleMachinePrec.VariableCost.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:31:06.517792+00:00
-- url     : https://prove2.me/theorems/d37c99cb-a774-4a5c-8585-32df4e839122
-- title:
--   Theorem 8.1 — approximating the variable cost of $1|\mathrm{prec}|\sum w_jC_j$ is as hard as approximating vertex cover
-- statement:
--   Let $G = (V,E)$ be a graph on $n$ vertices $v_1,\dots,v_n$, with vertex cover number $\tau(G)$. Let $r \ge 1$ and $\varepsilon > 0$, and let $k \ge 1$ satisfy
--   $$
--   k > \frac{n^2 r}{\varepsilon}.
--   $$
--   Let $S = S(G,k)$ be the scheduling instance of the proof of Theorem 8.1, and let $\tau_w(G^S_{\mathbf P})$ be the minimum weight of a vertex cover of its vertex cover graph $G^S_{\mathbf P}$ (the optimal variable cost). Let $C$ be a vertex cover of $G^S_{\mathbf P}$ with $w(C) \le r\,\tau_w(G^S_{\mathbf P})$, and put
--   $$
--   C_G = \{ v_i : (v'_i, v''_i) \in C \}.
--   $$
--   Then:
--
--   1. $C_G$ is a vertex cover of $G$;
--   2. $|C_G| \le r\left(\tau(G) + \dfrac{n^2}{k}\right)$;
--   3. if $E \neq \emptyset$, then
--   $$
--   |C_G| \le r\left(1 + \frac{n^2}{k}\right)\tau(G) < (r + \varepsilon)\,\tau(G).
--   $$
--
--   The paper states: "Approximating the variable cost of $1|\mathrm{prec}|\sum w_jC_j$ is as hard as approximating vertex cover", and concludes that an $r$-approximation algorithm for the variable cost would give an approximation algorithm for vertex cover with ratio $r(1+n^2/k) < r + \varepsilon$. Its proof establishes the statement above, which is what is formalized: any $r$-approximate solution of the variable-cost problem on $S(G,k)$ is turned, by the explicit map $C \mapsto C_G$, into an $(r+\varepsilon)$-approximate vertex cover of $G$. Together with Theorem 2.1 of the paper (cited from Ambühl–Mastrolilli and Correa–Schulz: an $\alpha$-approximate vertex cover of $G^S_{\mathbf P}$ can be turned in polynomial time into an $\alpha$-approximate solution of $S$), this shows that the variable cost is no easier to approximate than vertex cover.
--
--   **Formalization Note** The algorithmic wording ("approximation algorithm", polynomial time) and the cited Theorem 2.1 are not formalized; the size of $S(G,k)$ (polynomial in $n$ and $\log k$) is evident from the definition. The hypothesis $k \ge 1$ is implicit on the page: "$k > n^2r/\varepsilon$" does not imply it when $\varepsilon$ is large. The additive bound (2) is stated for every graph, and the multiplicative bound (3) only when $G$ has an edge, since otherwise $\tau(G) = 0$ and the strict inequality fails. $\tau(G)$ is Mathlib's `vertexCoverNum`, an extended natural number that is finite for a finite graph, converted with `toNat`.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 664, Theorem 8.1 and its proof

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_AdjacencyInstance
open scoped NNReal

namespace SingleMachinePrec.VariableCost

open Classical in
/-- Theorem 8.1 (p. 664): approximating the variable cost of `1|prec|∑ w_j C_j` is as hard as
approximating vertex cover. What the proof establishes: let `G` be a graph on `n` vertices,
`r ≥ 1`, `ε > 0`, `k > n² r / ε` with `k ≥ 1`, and `S = adjacencyInstance G k`. If `C` is a
vertex cover of `G^S_P` whose weight is at most `r` times the minimum weight of a vertex cover of
`G^S_P`, then `C_G = {v_i : (v′_i, v″_i) ∈ C}` is a vertex cover of `G` with
`|C_G| ≤ r (τ(G) + n²/k)`, and, if `G` has an edge, `|C_G| ≤ r (1 + n²/k) τ(G) < (r + ε) τ(G)`,
where `τ(G)` is the vertex cover number of `G`. -/
theorem theorem_8_1 {n : ℕ} (G : SimpleGraph (Fin n)) (r ε : ℝ) (k : ℝ≥0)
    (hr : 1 ≤ r) (hε : 0 < ε) (hk1 : 1 ≤ k) (hk : (n : ℝ) ^ 2 * r / ε < (k : ℝ))
    (C : Finset (IncPair (adjacencyInstance G k).P))
    (hC : (vertexCoverGraph (adjacencyInstance G k).P).IsVertexCover (C : Set _))
    (hCr : weight (adjacencyInstance G k) C ≤ r * minCoverWeight (adjacencyInstance G k)) :
    G.IsVertexCover {i | heavy G k i ∈ C} ∧
    ((Finset.univ.filter (fun i => heavy G k i ∈ C)).card : ℝ) ≤
      r * ((G.vertexCoverNum.toNat : ℝ) + (n : ℝ) ^ 2 / (k : ℝ)) ∧
    (G.edgeSet.Nonempty →
      ((Finset.univ.filter (fun i => heavy G k i ∈ C)).card : ℝ) ≤
          r * (1 + (n : ℝ) ^ 2 / (k : ℝ)) * (G.vertexCoverNum.toNat : ℝ) ∧
        r * (1 + (n : ℝ) ^ 2 / (k : ℝ)) * (G.vertexCoverNum.toNat : ℝ) <
          (r + ε) * (G.vertexCoverNum.toNat : ℝ)) := by sorry

end SingleMachinePrec.VariableCost
