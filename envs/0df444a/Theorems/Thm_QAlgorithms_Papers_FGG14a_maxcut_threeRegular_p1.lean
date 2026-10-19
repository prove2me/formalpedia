-- Prove2me | Theorems.Thm_QAlgorithms_Papers_FGG14a_maxcut_threeRegular_p1
-- name    : QAlgorithms.Papers.FGG14a.maxcut_threeRegular_p1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:46:16.386472+00:00
-- url     : https://prove2.me/theorems/84cff7a3-1d17-4692-834b-5acdda0e86bd
-- title:
--   p = 1 QAOA on connected 3-regular graphs reaches at least 0.6924 of the maximum cut
-- statement:
--   This is the headline MaxCut guarantee of the Quantum Approximate Optimization Algorithm (QAOA) at depth $p = 1$.
--
--   Let $G = (V, E)$ be a connected $3$-regular simple graph on $n$ vertices. For a bit string $z \in \{0,1\}^n$ let $C(z)$ be the number of edges $\langle jk \rangle \in E$ with $z_j \ne z_k$; as an operator, $C = \sum_{\langle jk\rangle \in E} \tfrac12 (1 - \sigma^z_j \sigma^z_k)$ is diagonal in the computational basis. Let $B = \sum_{j=1}^n \sigma^x_j$, let $|s\rangle = 2^{-n/2} \sum_z |z\rangle$ be the uniform superposition, and for angles $\gamma, \beta$ let
--
--   $$
--   |\gamma, \beta\rangle = e^{-i\beta B} e^{-i\gamma C} |s\rangle, \qquad F_1(\gamma, \beta) = \langle \gamma, \beta | C | \gamma, \beta \rangle = \sum_{z} |\langle z | \gamma, \beta\rangle|^2 \, C(z),
--   $$
--
--   the expected cut value of the string obtained by measuring $|\gamma,\beta\rangle$ in the computational basis. Then there exist angles $\gamma \in [0, 2\pi]$ and $\beta \in [0, \pi]$ such that
--
--   $$
--   F_1(\gamma, \beta) \ge 0.6924 \cdot \max_{z \in \{0,1\}^n} C(z).
--   $$
--
--   Equivalently, $M_1 = \max_{\gamma,\beta} F_1(\gamma,\beta)$ is at least $0.6924$ times the size of the maximum cut. The constant $0.6924$ is the numerically computed (rounded-down) worst-case ratio, attained in the limit of graphs without triangles; the source's derivation is partly numerical.
--
--   **Formalization Note** The graph is a `SimpleGraph (Fin n)` with `Connected` and `IsRegularOfDegree 3`. The approximation ratio is measured, as in the source's argument (34), through the expectation $F_1$ at the best angles; the source's informal remark that order $n \log n$ repetitions find a string with cut value near $M_1$ is not part of the statement.
-- source:
--   A Quantum Approximate Optimization Algorithm (Farhi, Goldstone, Gutmann), arXiv:1411.4028v1, Abstract and §V (unnumbered), PDF p. 9. https://arxiv.org/abs/1411.4028v1 . PDF SHA-256: 0b8f8649ffa0ae294d74a5d67a2198754283aa397771cc5b8c72161f3d1bb0a3.

import Definitions.Def_QAlgorithms_Defs_QAOA
set_option autoImplicit false

namespace QAlgorithms.Papers.FGG14a

/-- FGG p.1 (Abstract) and §V, pp.8–10, eqs. (32)–(35): for `p = 1`, on every connected
3-regular graph `G` on `n` vertices, the best `p = 1` QAOA angles give an expected cut value
`M_1 = max_{γ, β} F_1(γ, β)` that is at least `0.6924` times the maximum cut `max_z C(z)`.
The angles range over the source's intervals `γ ∈ [0, 2π]` (p.2) and `β ∈ [0, π]` (p.2).
The source's value `0.6924` is the (rounded-down) numerical minimum of (35). -/
theorem maxcut_threeRegular_p1 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree 3) :
    ∃ γ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∃ β ∈ Set.Icc (0 : ℝ) Real.pi,
      qaoaExpectation (fun z => (cutValue G z : ℝ)) 1 ![β] ![γ] ≥
        0.6924 * ((Finset.univ.sup fun z : Qubits n => cutValue G z : ℕ) : ℝ) := by
  sorry

end QAlgorithms.Papers.FGG14a
