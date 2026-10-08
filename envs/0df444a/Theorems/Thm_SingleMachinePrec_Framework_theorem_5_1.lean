-- Prove2me | Theorems.Thm_SingleMachinePrec_Framework_theorem_5_1
-- name    : SingleMachinePrec.Framework.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:49:46.618991+00:00
-- url     : https://prove2.me/theorems/c20a288f-4a57-4980-a201-27f0d6e8333c
-- title:
--   Theorem 5.1 — a k : t-realizer rounds a half-integral optimal [CS-LP] solution to vertex covers of average weight ≤ (2 − 2/(t/k)) OPT
-- statement:
--   The paper states: *the problem $1|\mathrm{prec}|\sum w_jC_j$, whenever precedence constraints admit an efficiently samplable $k:t$-realizer, has a randomized $(2-2/(t/k))$-approximation algorithm.* Its proof establishes the following guarantee for the vertex cover formulation, which is what is formalized.
--
--   Let $S$ be an instance of $1|\mathrm{prec}|\sum w_jC_j$ with jobs $N$, nonnegative processing times $p_j$ and weights $w_j$, and precedence order $P$; let $G^S_P$ be its vertex cover graph with node weights $w_{(i,j)} = p_iw_j$, and $\mathrm{OPT}$ the minimum weight of a vertex cover of $G^S_P$. Let $L_1,\dots,L_t$ be a $k:t$-realizer of $P$ and $x$ a half-integral optimal solution of [CS-LP], with $V_a = \{u : x_u = a\}$. For each $i$ put
--   $$C_i = V_1 \cup \bigl(V_{1/2} \setminus I_{1/2}(L_i)\bigr),$$
--   where $I_{1/2}(L_i)$ is the set of incomparable pairs of $V_{1/2}$ reversed in $L_i$. Then
--   1. every $C_i$ is a vertex cover of $G^S_P$, and
--   2. the expected weight of $C_i$ for $i$ drawn uniformly from $\{1,\dots,t\}$ satisfies
--   $$\frac1t \sum_{i=1}^t w(C_i) \;\le\; \Bigl(2 - \frac{2}{t/k}\Bigr)\,\mathrm{OPT}.$$
--
--   Combined with Theorem 2.1 (a vertex cover of $G^S_P$ can be turned into a schedule with the same approximation ratio) this is the paper's $(2-2/f)$-approximation framework for precedence constraints of fractional dimension $f$.
--
--   **Formalization Note** "Efficiently samplable", "polynomial time" and "randomized algorithm" are not formalized: the randomization is the uniform average over the realizer's indices. The existence of a half-integral optimal [CS-LP] solution (Nemhauser–Trotter, cited on p. 659) is taken as a hypothesis on $x$, and the passage from a cover of $G^S_P$ to a schedule (Theorem 2.1, cited) is not formalized. The paper's assumption $\operatorname{fdim}(P) \ge 2$ is not needed: if $P$ is a linear order there are no incomparable pairs and both sides are $0$.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 658, Theorem 5.1; proof p. 659

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_CSLP

namespace SingleMachinePrec.Framework

/-- **Theorem 5.1** (p. 658; proof p. 659), the guarantee its proof establishes. Let `S` be an
instance of `1|prec|∑ w_j C_j`, `L_1, …, L_t` a `k : t`-realizer of its precedence order `P`, and
`x` a half-integral optimal solution of [CS-LP]. For each `i` let
`C_i = V_1 ∪ (V_{1/2} \ I_{1/2}(L_i))`, where `I_{1/2}(L_i)` is the set of pairs of `V_{1/2}`
reversed in `L_i`. Then
(a) every `C_i` is a vertex cover of `G^S_P`, and
(b) the average weight `(1/t) ∑_i w(C_i)` (the expected weight when `L` is drawn uniformly from
the realizer) is at most `(2 - 2/(t/k)) · OPT`, where `OPT` is the minimum weight of a vertex
cover of `G^S_P`. -/
theorem theorem_5_1 {N : Type*} [Fintype N] [DecidableEq N] (S : Instance N) (k t : ℕ)
    (L : Fin t → LinearExtension S.P) (hL : IsKFoldRealizer S.P k t L)
    (x : IncPair S.P → ℝ) (hx : IsCSLPOptimal S x) (hhalf : IsHalfIntegral x) :
    (∀ i, (vertexCoverGraph S.P).IsVertexCover (roundedCover x (L i) : Set (IncPair S.P))) ∧
      (1 / (t : ℝ)) * ∑ i, weight S (roundedCover x (L i)) ≤ (2 - 2 / ((t : ℝ) / k)) * OPT S := by sorry

end SingleMachinePrec.Framework
