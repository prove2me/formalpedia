-- Prove2me | Theorems.Thm_PaceSSSP517_Certified_worst_case
-- name    : PaceSSSP517.Certified.worst_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:41.389358+00:00
-- url     : https://prove2.me/theorems/90ac5949-1c4f-4795-b3c9-35ebdc17e802
-- title:
--   Theorem 3.6 — Full certified worst-case guarantee
-- statement:
--   Fix a one-pass spanner implementation with uniform size and workspace constant $C_H$. There exist positive constants $C_1,C_2$, depending only on that fixed implementation and word layout, such that the following holds for every finite connected simple graph with arbitrary positive real weights, every source $s_0$, every insertion stream order and all parameters $k\ge2$, $0<\varepsilon<1$, $k\le\ln n$, $12k^2\le\varepsilon n$. Put
--
--   $$s=(20/\varepsilon)kn^{1+1/k}\ln n,\qquad R_{\rm wc}=\lceil11k^2/\varepsilon\rceil.$$
--
--   With probability at least
--
--   $$1-R_{\rm wc}n^{-n}-R_{\rm wc}\exp(-s/3),$$
--
--   all of the following hold jointly for Algorithm 1's actual executed prefix:
--
--   1. Every edge fails in at most $6k$ executed rounds.
--   2. It stops at $1\le R\le R_{\rm wc}$. Its actual returned tree $T_R$ spans the graph and realizes $d_R$, and every vertex satisfies $\operatorname{dist}_G(s_0,x)\le d_R(x)\le(1+\varepsilon)\operatorname{dist}_G(s_0,x)$. True weighted distance minima are finite and attained.
--   3. The number $V_R$ of actually stored bulk violators satisfies $V_R\le\min\{m,Rs/2\}$. For every choice of subsequent pass orders, actual peak allocated words, including transient samples, the bounded violator buffer, local shortest-path workspace, suffix scratch and the initial spanner pass, satisfy
--
--   $$\mathrm{peakWords}\le C_1(s+Rn+V_R),\qquad
--   \mathrm{peakWords}\le C_2\varepsilon^{-2}k^3n^{1+1/k}\ln n.$$
--
--   4. The pass count is $2R+1$.
--
--   The probability is unconditional under the adaptive product-kernel law. Its success event contains the returned tree, all vertices and edges, stopping, and every resource clause simultaneously. The constants are chosen before all graph, weight, parameter, stream and trajectory inputs. The spanner's unspecified uniform constant is kept symbolic, rather than assigned an invented numeral.
--
--   Differences from the source:
--   - encoding: finite undirected positive-real weighted graphs and one-based rounds → Fin n vertices, each edge stored once with its smaller endpoint first, and list position j-1 for round j; source vertex s₀ and real sample budget s; reason: these are bijective naming and indexing conventions; no parallel edges or weight restriction is added
--   - encoding: compute exact source distances and a shortest-path tree of the observed subgraph → n-1 synchronous local Bellman–Ford relaxations and the least numbered tight predecessor at each non-source vertex; reason: this fixes a permitted deterministic tie rule using only the observed subgraph; its exactness and finite path realization are proof obligations, not run assumptions
--   - encoding: real lower bound on success probability → normalized finite-support PMF probability in ENNReal, lower bounded by ENNReal.ofReal of the stated real expression; reason: when the displayed real lower bound is negative both assertions are automatic; otherwise ofReal preserves the inequality exactly
--   - encoding: the loop stops before line 6 and Appendix A.5 uses weights through the round cap → a virtual update recursion followed by its prefix through the first stop; later virtual rounds and the terminal virtual update are not executed or charged; reason: the projected law has exactly the original conditional kernels before stopping and absorbing output thereafter; only its executed prefix enters the goal
--   - encoding: connected graphs and finite computed shortest-path distances → ENNReal path infima with real profiles and explicit finiteness and attained-path conclusions; reason: empty path families have genuine infinite distance; the connected positive-weight source instances have attained finite minima, so no default toReal value can satisfy the goal
--   - encoding: O(s+Rn+V_R) and O(ε^(-2) k^3 n^(1+1/k) log n) words → positive constants C₁,C₂ precede every input and bound explicitly allocated banks, including spanner-pass peak; V_R counts committed bulk pins only; reason: the fixed layout has 3-word edge records, n-word profiles and constant-factor adjacency, search, buffer, metadata and suffix scratch; p.6 and A.5 give the underlying components; line 5 stops before the terminal update
--   - encoding: the one-pass spanner construction is invoked as an external primitive → a separate single-fold SpannerRoutine with its uniform construction, size and peak-space interface; reason: AHS26 Proposition 3.2 supplies precisely this upstream contract; the interface assumes no PACE conclusion and C_H is fixed before all inputs
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 7, Theorem 3.6; p. 18, Appendix A.5

import Definitions.Def_PaceSSSP517_Certified_Resources

set_option autoImplicit false
open scoped ENNReal NNReal

namespace PaceSSSP517.Certified

/-- Theorem 3.6, p.7; proof A.5 p.18, all clauses. Constants are chosen
before every graph, weight, parameter and execution. The only upstream interface
is the separate one-pass spanner primitive; no PACE success property is assumed. -/
theorem worst_case (A : SpannerRoutine) (C_H : ℝ) (hA : SpannerInterface A C_H) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n k : ℕ) (ε : ℝ) (G : WeightedGraph n) (s₀ : Fin n)
        (σ : List (Edge n)),
        Parameters n k ε → Connected G.edges → StreamOf G σ →
        let H := spannerOutput A G k ε σ
        let Rwc := roundCap k ε
        ENNReal.ofReal (1 - (Rwc : ℝ) * ((n : ℝ)^n)⁻¹ -
          (Rwc : ℝ) * Real.exp (-budget n k ε / 3)) ≤
        probability (runLaw G H s₀ k ε Rwc)
          {ts |
              (∀ e ∈ G.edges, failureCount G ts e ≤ 6 * k) ∧
              1 ≤ ts.length ∧ ts.length ≤ roundCap k ε ∧ stopped ts ∧
              (∃ t, ts.getLast? = some t ∧
                t.tree ⊆ G.edges ∧ Connected t.tree ∧ t.tree.card + 1 = n ∧
                ∀ x, edistance G G.edges s₀ x ≠ ⊤ ∧
                  (∃ p, IsWalk G.edges s₀ x p ∧ pathCost G p = distance G G.edges s₀ x) ∧
                  distance G G.edges s₀ x ≤ t.d x ∧
                  t.d x ≤ (1 + ε) * distance G G.edges s₀ x ∧
                  edistance G t.tree s₀ x = ENNReal.ofReal (t.d x)) ∧
              Vcount G ts ≤ G.edges.card ∧ (Vcount G ts : ℝ) ≤ ts.length * budget n k ε / 2 ∧
              (∀ orders : ℕ → List (Edge n), (∀ r, StreamOf G (orders r)) →
                (peakWords G H k ε (spannerPeak A G k ε σ) orders ts : ℝ) ≤
                  C₁ * (budget n k ε + ts.length * n + Vcount G ts) ∧
                (peakWords G H k ε (spannerPeak A G k ε σ) orders ts : ℝ) ≤
                  C₂ * (ε⁻¹^2 * (k : ℝ)^3 * (n : ℝ)^(1 + 1/(k : ℝ)) * Real.log n)) ∧
              passCount ts = 2 * ts.length + 1          } := by sorry

end PaceSSSP517.Certified
