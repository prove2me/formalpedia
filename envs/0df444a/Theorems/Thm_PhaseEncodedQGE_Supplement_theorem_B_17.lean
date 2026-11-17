-- Prove2me | Theorems.Thm_PhaseEncodedQGE_Supplement_theorem_B_17
-- name    : PhaseEncodedQGE.Supplement.theorem_B_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:34:12.254918+00:00
-- url     : https://prove2.me/theorems/45589357-af83-4252-ba62-cc4d7e1f89f5
-- title:
--   Theorem B.17 — cubic second-purity motif closure with $b_3=3(v_1-v_0)$, $b_4=2\delta_0$, $b_D=\delta_1-\delta_0$
-- statement:
--   Under PE-X1 (degree-aware preparation, one $X$ mixer), let $M_2''(G;0)$ be the second $\beta$-derivative at $0$ of the output purity $\sum_x p_G(x;\beta)^2$, and let $F_{a,k}$ be the pair kernel (53) of a vertex pair of class $(a,k)$ (adjacency $a$, codegree $k$). For every simple cubic graph $G$ of order $n$, and for angles in the domain of the kernel formulas,
--   $$M_2''(G;0)=A_n+b_3C_3(G)+b_4C_4(G)+b_DD_\diamond(G),$$
--   where the coefficients depend on $(n,\eta,\gamma)$ but not on $G$. With
--   $$v_a=F_{a,1}-F_{a,0},\qquad \delta_a=F_{a,2}-2F_{a,1}+F_{a,0},$$
--   one has
--   $$b_3=3(v_1-v_0),\qquad b_4=2\delta_0,\qquad b_D=\delta_1-\delta_0.$$
--
--   The second-order purity is thus an affine function of the triangle, four-cycle and $K_4-e$ counts with explicit coefficients, so it separates cospectral cubic graphs that differ in $D_\diamond$ whenever $b_D\ne0$.
--
--   **Formalization Note** $C_3$, $C_4$ count cycles as subgraphs ($C_4$ includes chorded four-cycles) and $D_\diamond$ counts not necessarily induced copies of $K_4-e$. $F_{a,k}$ is the mission's class kernel at the preparation $|\chi(\eta,-\pi/2)\rangle=R_X(\eta)|0\rangle$.
--
--   Differences from the source:
--   - reading: "for angles in the domain of the kernel formulas" → every $\eta,\gamma\in\mathbb R$; reason: Remark B.18: at isolated zeros of carrier denominators the coefficients are defined by continuous extension of the finite spin sum; the kernels here are finite spin sums, defined everywhere
--   - encoding: $F_{a,k}$, the kernel (53) of a pair of class $(a,k)$ → $L^{n-N}$ times the kernel (53) of the roots of the local motif of class $(a,k)$ under $|\chi(\eta,-\pi/2)\rangle^{\otimes N}$; reason: it equals the kernel of every class-(a,k) pair of every cubic graph on n vertices (Corollary B.4), and is defined at every n for every class, as (66)–(67) require
--   - encoding: $A_n$ "depending on $(n,\eta,\gamma)$ but not on $G$" → $\exists A$ for each $(n,\eta,\gamma)$, before $\forall G$; reason: that is the meaning of a graph-independent coefficient
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. B.2.5, p.32 (PDF p.33), Theorem B.17, eqs. (65)–(67); kernel (53), p.30 (PDF p.31); Lemma B.16, p.31 (PDF p.32); Remark B.18, p.33 (PDF p.34)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
import Definitions.Def_PhaseEncodedQGE_Supplement_GraphCounts
import Definitions.Def_PhaseEncodedQGE_Supplement_Purity
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

/-- Theorem B.17, cubic second-purity motif closure (Miller, Lee, *Structural Accessibility in
Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. B.2.5,
p.32, eqs. (65)–(67); Remark B.18, p.33).

For every simple cubic graph `G` of order `n`, and for angles in the domain of the kernel formulas,
`M″₂(G; 0) = A_n + b₃ C₃(G) + b₄ C₄(G) + b_D D⋄(G)`, where the coefficients depend on `(n, η, γ)` but
not on `G`. With `v_a = F_{a,1} − F_{a,0}` and `δ_a = F_{a,2} − 2F_{a,1} + F_{a,0}`, one has
`b₃ = 3(v₁ − v₀)`, `b₄ = 2δ₀`, `b_D = δ₁ − δ₀`.

**Formalization Note** PE-X1: degree-aware preparation (`R_X(η)` on every vertex of a cubic
graph), `X` mixer, one repetition, mixer-phase angle `γ`. `M″₂(G; 0)` is `purityCurv`, the second
`β`-derivative of `∑_x p_G(x; β)²` at `0`. `F_{a,k}` is `classKernel η (−π/2) γ n a k`, the pair
kernel (53) of a class-`(a, k)` pair computed on its local motif times the spectator factor
`L^{n−N}`, `L = c⁴ + s⁴` (`R_X(η)|0⟩ = |χ(η, −π/2)⟩`); `b₃`, `b₄`, `b_D` are the explicit
`closureB3`, `closureB4`, `closureBD`, never chosen. `A_n` is existentially quantified for each
`(n, η, γ)` before the graph. `C₃`, `C₄` are subgraph cycle counts (`C₄` counts all simple
four-cycles, chorded ones included) and `D⋄` the number of not necessarily induced `K₄ − e`
subgraphs. The kernels are finite spin sums, defined at every angle; Remark B.18 extends the
theorem to the isolated zeros of carrier denominators by continuity, so it is stated for all
`η, γ ∈ ℝ`. -/
theorem theorem_B_17 :
    ∀ (n : ℕ) (η γ : ℝ), ∃ A : ℝ, ∀ G : SimpleGraph (Fin n), IsCubic G →
      purityCurv (degPrep G η) .X 1 G γ =
        A + closureB3 η (-(Real.pi / 2)) γ n * (cycleCount G 3 : ℝ) +
          closureB4 η (-(Real.pi / 2)) γ n * (cycleCount G 4 : ℝ) +
          closureBD η (-(Real.pi / 2)) γ n * (diamondCount G : ℝ) := by sorry

end PhaseEncodedQGE.Supplement
