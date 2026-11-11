-- Prove2me | Theorems.Thm_PrivateRoutingSignaling_PTAS_bicriteria_ptas
-- name    : PrivateRoutingSignaling.PTAS.bicriteria_ptas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:53:48.873971+00:00
-- url     : https://prove2.me/theorems/5259d865-1fd5-4c0a-a9c7-9f2abe971344
-- title:
--   Theorem 1.1 / 3.2 — bicriteria PTAS with charged binary runtime
-- statement:
--   For a finite directed routing network with $n$ labelled arcs, let $d$ bound every simple source-sink path's length. The finite nonempty state set $\Theta$ has a rational prior, possibly with zero entries. Each state's arc latencies are nonnegative, nondecreasing and continuous on $[0,1]$, with a known common Lipschitz bound $L\ge0$. Finite binary descriptions evaluate these functions exactly at rational loads, returning rationals in polynomial time.
--
--   There is one uniform executable pipeline and positive universal constants $A,a,b,C$, independent of the graph, latency descriptions, evaluation-envelope degree, $L$, and requested error, with the following guarantee. For every positive rational tolerance $\delta$ and rational Lipschitz bound, it constructs the entire grid LP, computes an exact optimal rational basic solution, and emits a finite rational scheme $\varphi'$. With $\operatorname{OPT}$ defined over all exactly obedient Borel schemes on arbitrary real flows,
--
--   $$\operatorname{SC}(\varphi')\le\operatorname{OPT}+\delta,$$
--   $$\int s_p\bigl(c_q^\theta(s)+\delta-c_p^\theta(s)\bigr)\,d\varphi'\ge0\quad(p\ne q).$$
--
--   The state marginal equals the prior exactly. The goal also proves cost and obedience integrability, arc-load domain facts, and finite attainment of the exact benchmark from the standing assumptions.
--
--   The three stages build $(P_\epsilon)$, solve it, and format its solution, using $k=\max\{1,\lceil4d_{\max}^2L/\delta\rceil\}$, where $d_{\max}\le d$ is the graph's actual maximum path length; $d$ itself is not part of the input. Every stage is a finite binary-tape program. Actual transitions and data handoffs are bounded by
--
--   $$A(1+B+E(A(1+B+\log_2(k+1))^b))^b(1+|\Theta|)^a\max\{2,n\}^{\lceil C(d+d^3L/\delta)\rceil},$$
--
--   where $B$ is the complete input's bit length and $E$ is any valid monotone polynomial envelope for exact latency evaluation. Its degree need not be uniform across descriptions. The logarithm in the formal budget is the integer base-two logarithm. The LP solver is not assumed as an input.
--
--   For every real requested accuracy $\varepsilon>0$ and real known bound $L$, the same pipeline also satisfies the bound with $L,\varepsilon$ in its exponent: choose rational $l$ with $L\le l\le2L$ and $\delta\in(\varepsilon/2,\varepsilon)$. This includes $L=0$ with $l=0$ and grid denominator one. The output is a bicriteria $\varepsilon$-approximation. Thus the result retains the source's full $\operatorname{poly}(|\Theta|)n^{O(d+d^3L/\varepsilon)}$ dependence with suppressed input and evaluation factors. The theorem asserts a PTAS at fixed $d,L,\varepsilon$, not an FPTAS.
--
--   Differences from the source:
--   - encoding: finite graph and all simple source-sink paths → Fin graph indices, graph-derived bounded arc-word enumeration, and the empty path for coincident terminals; reason: parallel arcs and cycles remain represented and the path-length hypothesis ensures the enumeration is exhaustive
--   - encoding: all joint distributions over states and real simplex flows, with a finite attained optimum → Borel measures on the real simplex and an EReal infimum, with finite attainment and all required integrability as conclusions; reason: the benchmark is unchanged and no total real-infimum or nonintegrable-integral default can justify the guarantees
--   - generalization: there is an algorithm that computes a bicriteria approximation in the stated time → the pipeline's stages must output exactly the encoded grid LP (P_ε) with k=max(1,ceil(4d²L/δ)) for the graph's maximum path length d, an optimal basic solution of it, and its sparse encoding; reason: this is the paper's §3.1 algorithm with the universal constant of pp. 11–12 made explicit (the 2d/k load bound yields 2d²L/k path and cost errors and 4d²L/k conditional incentive error); at L=0 the k=1 grid LP replaces the paper's minimum-constant-latency path rule and loses nothing since constant latencies make rounding cost-free; forgetting the intermediate outputs gives the source's claim
--   - encoding: d, the maximum number of arcs on a simple source-sink path → a bound N.d on every simple path's length that is not part of the machine input, with the grid denominator computed from the graph's actual maximum path length; reason: Theorem 3.2 states its runtime for any such bound and Theorem 1.1 for the maximum, which is one admissible value; the algorithm is told L but not d, as on p. 3
--   - encoding: poly(|Θ|) times n to O(d+d³L/ε), suppressing input and evaluation factors → a fixed pipeline of three finite bit-machine tables with counted transitions and handoffs and explicit universal A,a,b,C in timeBudget; reason: the polynomial overhead and small-size shifts express the full bound; arbitrary evaluator polynomial degrees are retained in E and no solver correctness or speed is a hypothesis
--   - encoding: rational binary data and finite latency descriptions permitting exact polynomial evaluation → framed binary numbers and finite evaluator transition tables; sparse path-and-probability output from an optimal basic grid LP solution; reason: these are conventional finite executable descriptions, with all evaluation and output work charged; a source description with a polynomial evaluator can be compiled into a fixed-tape evaluator with polynomial overhead
--   - encoding: every real requested accuracy ε and known real Lipschitz bound L → both a rational binary-input clause and a real-target clause choosing ε/2<δ<ε and L≤l≤2L, including zero; reason: rational density preserves every target and known bound with only universal factors in the exponent; the mathematical optimum remains over real flows
--   - encoding: obedience constraints for distinct p,q in P_ε → also include the diagonal rows in the constructed LP; reason: at positive tolerance and nonnegative grid weights each diagonal inequality is automatic, so the feasible set is identical
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #439 (October 2026), Theorem 1.1, p. 3 (PDF p. 3), restated as Theorem 3.2, p. 11 (PDF p. 11); proof pp. 11–12; standing assumptions and computation conventions §§2–3, pp. 5–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Computation

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS

/-- Theorem 1.1 = Theorem 3.2. One fixed composition of finite binary programs; universal degrees precede
all instance, evaluator, accuracy and Lipschitz quantifiers. No LP solver is an input.
The real-parameter clause retains every real accuracy and real Lipschitz bound. -/
theorem bicriteria_ptas :
    ∃ (P : Pipeline) (A a b C : ℕ),
      0 < A ∧ 0 < a ∧ 0 < b ∧ 0 < C ∧
      ∀ (I : Instance) (D : BinaryData I) (E : ℕ → ℕ), Evaluates I D E →
        (∀ (L ε : ℚ), Standing I (L : ℝ) → 0 < ε →
          Wellposed I ∧
          let k := gridSize (maxPathLength I.network) L ε
          ∃ (hk : 0 < k) (w : GridColumn I k → ℚ) (order : List (GridColumn I k)),
            OutputOrder I k w order ∧
            PipelineRuns P I D L ε k w order
              (timeBudget A a b C I E (inputCode I D L ε).length k (L : ℝ) (ε : ℝ)) ∧
            OptimalBasic I D k ε w ∧
            Bicriteria I (ε : ℝ) (outputMeasure I k hk w)) ∧
        (∀ (L ε : ℝ), Standing I L → 0 < ε →
          Wellposed I ∧
          ∃ (l δ : ℚ), L ≤ (l : ℝ) ∧ (l : ℝ) ≤ 2 * L ∧
            ε / 2 < (δ : ℝ) ∧ (δ : ℝ) < ε ∧
            let k := gridSize (maxPathLength I.network) l δ
            ∃ (hk : 0 < k) (w : GridColumn I k → ℚ) (order : List (GridColumn I k)),
              OutputOrder I k w order ∧
              PipelineRuns P I D l δ k w order
                (timeBudget A a b C I E (inputCode I D l δ).length k L ε) ∧
              OptimalBasic I D k δ w ∧
              Bicriteria I ε (outputMeasure I k hk w)) := by sorry

end PrivateRoutingSignaling.PTAS
