-- Prove2me | Theorems.Thm_PlantedSubgraphLD_Supplement_theorem_1_2
-- name    : PlantedSubgraphLD.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:59:21.296222+00:00
-- url     : https://prove2.me/theorems/f115577e-8f9e-4162-a34f-3a0c8c102f87
-- title:
--   Theorem 1.2 — for $c\le 1$, low-degree indistinguishability implies $\|T_\varepsilon P_n-Q_n\|_{\mathrm{TV}}\to 0$ without a treewidth condition
-- statement:
--   Fix $c\in(0,1]$. Let $Q_n=G(n,c/n)$ be the Erdős–Rényi null law on graphs with vertex set $[n]$. Let $(\Gamma_n)_{n\ge1}$ be **any** sequence of simple graphs, $\Gamma_n$ having at most $n$ vertices, and let $P_n$ be the planted law: the union of a sample of $Q_n$ with a uniformly random injective copy of $\Gamma_n$ in $[n]$. For $\varepsilon\in(0,1)$, $T_\varepsilon$ resamples each edge indicator independently with probability $\varepsilon$ from Bernoulli$(c/n)$. Write $L_n=dP_n/dQ_n$ and $L_n^{\le D}$ for its orthogonal projection in $L^2(Q_n)$ onto polynomials of degree at most $D$ in the edge indicators.
--
--   Suppose there is a sequence of integers $D_n$ with $D_n=\omega(\log n)$ such that the low-degree condition (1.3) holds:
--
--   $$
--   \|L_n^{\le D_n}\|^2_{L^2(Q_n)}\longrightarrow 1 .
--   $$
--
--   Then for every fixed $\varepsilon\in(0,1)$, the conclusion (1.5) holds:
--
--   $$
--   \|T_\varepsilon P_n-Q_n\|_{\mathrm{TV}}\longrightarrow 0 .
--   $$
--
--   At and below the Erdős–Rényi critical point, low-degree indistinguishability at a superlogarithmic degree thus implies statistical indistinguishability after any constant amount of noise, for every deterministic planted family; unlike Theorem 1.1, no treewidth condition is needed.
--
--   **Formalization Note** $\Gamma_n$ is a graph on a finite vertex type $V_n$ with $|V_n|\le n$, as in the mission's Theorem 1.1. $D_n=\omega(\log n)$ is $\log n=o(D_n)$ along $n\to\infty$ (natural logarithm). Laws are real functions on the finite set of graphs on $[n]$, the low-degree norm is the variational form of the projection norm (`lowDegNormSq`), and $\|\cdot\|_{\mathrm{TV}}$ is $\sup_A|\mu(A)-\nu(A)|$ (`tvDist`).
--
--   Differences from the source:
--   - encoding: Γn a simple graph with at most n vertices → a graph on a finite type V n with card (V n) ≤ n; reason: same graphs up to relabeling, as in the published Theorem 1.1
--   - encoding: Dn = ω(log n), (1.3) ‖L≤Dn_n‖² = 1 + o(1), (1.5) ‖TεPn − Qn‖TV = o(1) → log n =o[atTop] Dn with Dn : ℕ, Tendsto of the published lowDegNormSq to 1 and of tvDist (noisedPlanted) (erdosRenyi) to 0; reason: Lean's asymptotic notation and the mission's published definitions; same instances
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §1.1, Theorem 1.2, p.4 (PDF p.6); (1.3) and (1.5), p.3 (PDF p.5)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_noisedPlanted
import Definitions.Def_PlantedSubgraphLD_lowDegNormSq
import Definitions.Def_PlantedSubgraphLD_tvDist

open Filter Asymptotics

namespace PlantedSubgraphLD.Supplement

open PlantedSubgraphLD

/-- **Theorem 1.2 (Critical and Subcritical Regimes).** Chen, Li, *Rigorous Low-Degree
Implications for Planted Subgraph Detection: Noise and Treewidth* (manuscript of Nov. 3, 2026,
arXiv:2608.06279, sha256 405d09c0…), §1.1, Theorem 1.2, p.4 (PDF p.6): "Fix c ∈ (0, 1], and let
{Γn}n≥1 be any sequence of simple graphs with at most n vertices. Suppose that Dn = ω(log n) and
(1.3) holds. Then, for every fixed ε ∈ (0, 1), the conclusion (1.5) holds."

Here (1.3) is `‖L≤Dn_n‖²_{L²(Qn)} = 1 + o(1)` and (1.5) is `‖TεPn − Qn‖TV = o(1)` (p.3).

**Formalization Note** Same encoding as the mission's `theorem_1_1_supercritical`: Γₙ is a graph
on a finite vertex type `V n` with `card (V n) ≤ n`; sequences are indexed by all `n : ℕ` (the
`n = 0` term does not affect a limit). `Dₙ = ω(log n)` is `log n = o(Dₙ)` along `atTop`
(natural logarithm, §3.1); `1 + o(1)` is convergence to `1` and `o(1)` convergence to `0`. No
treewidth hypothesis and no positivity of `Dₙ` is assumed (ω(log n) forces `Dₙ > 0` eventually).
Only (1.5) is concluded, as on the page. -/
theorem theorem_1_2 (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (V : ℕ → Type) [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (hV : ∀ n, Fintype.card (V n) ≤ n) (Γ : ∀ n, SimpleGraph (V n))
    (D : ℕ → ℕ)
    (hD : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n => (D n : ℝ)))
    (h13 : Tendsto (fun n => lowDegNormSq c n (Γ n) (D n)) atTop (nhds 1)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => tvDist (noisedPlanted c ε n (Γ n)) (erdosRenyi c n)) atTop (nhds 0) := by sorry

end PlantedSubgraphLD.Supplement
