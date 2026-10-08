-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_coupling_diam
-- name    : ScaleFreeDiam.Main.coupling_diam
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:07.206907+00:00
-- url     : https://prove2.me/theorems/3129ceae-a446-4a6e-a629-ffe6db447f81
-- title:
--   §6, p. 20 — G(W₁,…,W_n), W_i = R_{mi}, can be coupled with G_mⁿ so that G is G_mⁿ with edges deleted and loops added
-- statement:
--   Fix $m\ge2$ and $n\ge1$. Let $R_1\le\dots\le R_{mn}$ be the sorted values of $mn$ independent $M_2(0,1)$ random variables, $W_i=R_{mi}$, and let $G=G(W_1,\dots,W_n)$ be the random graph in which each vertex $i$ is joined to $l_{i,1}$ and $l_{i,2}$, independent with $\mathbb P(l_{i,j}=k)=w_k/W_i$ for $k\le i$. Then $G$ is stochastically dominated by $G_m^n$ in the subgraph order: for every property $\mathcal P$ of graphs on $[n]$ that is preserved under adding edges,
--   $$
--   \mathbb P\big(G\in\mathcal P\big)\le\mathbb P\big(G_m^n\in\mathcal P\big),
--   $$
--   where the left-hand side is the probability under the joint law of $(R,L)$, i.e. the average over $R$ of $\mathbb P_L(G(W)\in\mathcal P)$.
--
--   The paper states (end of §6) that $G$ can be coupled with $G_m^n$ so that $G$ is obtained from $G_m^n$ by deleting some edges and adding some loops. On the simple graphs underlying both (loops dropped), this says exactly that the law of $G$ is dominated by that of $G_m^n$ in the subgraph order; on the finite poset of graphs on $[n]$ such a coupling exists if and only if the inequality above holds for every up-closed property (Strassen's theorem). Taking $\mathcal P$ = "every two vertices are joined by a walk of length at most $x$" gives the consequence used on p. 29, $\mathbb P(\operatorname{diam}G_m^n>x)\le\mathbb P(\operatorname{diam}G>x)$.
--
--   **Formalization Note** The coupling is stated through the equivalent domination inequality over all up-closed properties, rather than as the existence of a joint probability space. Graphs are the simple-graph shadows (loops and multiple edges dropped), so "adding loops" is invisible. The left-hand side is a lower Lebesgue integral over the product law of $M_2(0,1)$; on the null set where $W$ is not strictly increasing below $1$ (ties, or a value outside $(0,1)$) the integrand is set to $0$.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 20, §6 (the coupling of G(W₁,…,W_n) with G_mⁿ); p. 29, proof of Theorem 1 (diam(G) ≥ diam(G_mⁿ))

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process
import Definitions.Def_ScaleFreeDiam_Main_EndpointModel

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem coupling_diam (m : ℕ) (hm : 2 ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (P : SimpleGraph (Fin n) → Prop) (hP : ∀ G H : SimpleGraph (Fin n), G ≤ H → P G → P H) :
    ∫⁻ r, ENNReal.ofReal
          (if Admissible n (Wof m n r) then
            probGW n (Wof m n r) (fun l => P (GW l))
          else 0)
        ∂(Measure.pi fun _ : Fin (m * n) => M2) ≤
      ENNReal.ofReal (probGm m n P) := by sorry

end ScaleFreeDiam.Main
