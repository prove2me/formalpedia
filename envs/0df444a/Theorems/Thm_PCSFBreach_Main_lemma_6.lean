-- Prove2me | Theorems.Thm_PCSFBreach_Main_lemma_6
-- name    : PCSFBreach.Main.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:50.113122+00:00
-- url     : https://prove2.me/theorems/a2ebd9e7-ab43-4497-b7ab-de9ce5ed1b7f
-- title:
--   Lemma 6 — contraction algorithm: cost ≤ 2y(H) + (α + ε)·st(𝒮) − (1 − e^{−α})·gain(𝒮) + π(Q)
-- statement:
--   Fix constants $\alpha\in[0,1]$ and $\varepsilon>0$. There is one polynomial-time computable function $M$ such that for every PCSF instance $J$ with nonnegative rational data, $M$ maps the code of $J$ to the code of a forest $F$ of $J$ such that for every run of the primal-dual algorithm with $\lambda=2$, $\mu=10^{-12}$ on $J$ (moats $H$, duals $y$, forced pairs $Q$) and every collection $\mathcal S$ of actively connected sets,
--   $$\mathrm{cost}(F)\le 2\cdot y(H)+(\alpha+\varepsilon)\cdot\mathrm{st}(\mathcal S)-(1-e^{-\alpha})\cdot\mathrm{gain}(\mathcal S)+\pi(Q).$$
--
--   This is the first ingredient of the bifactor algorithm: profitable contractions of actively connected sets.
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: a polynomial-time algorithm on (G, c, D, π) → one function M on binary strings with PolyTimeComputable M (published QAlgorithms_ClassicalStringComputability: Mathlib multi-stack Turing machine, time polynomial in the input length), fixed before the instance, mapping the binary code encInst J of every instance J with nonnegative rational costs and penalties to the characteristic vector encEdgeSet of its output edge set; reason: bit model; Appendix B (p. 47) assumes rational input data; the vertex count n is coded in unary (the input graph G = (V, E) lists its vertices) and every other number in binary, so the time bound is polynomial in |V| plus the bit length of the data; strings that code no instance are unconstrained
--   - encoding: a solution → an edge set F that is a forest of the instance (IsForest: no loop, no edge joining two vertices already connected by the other edges of F); reason: p. 1: a feasible solution is any forest F ⊆ E
--   - encoding: the run of §4–§8 on a fresh instance (λ = 2, µ = 10^-12, p. 12) → every run with IsPDRun I 2 (1/10^12) R; reason: the section's standing parameters, kept as printed
--   - encoding: the run of the primal-dual algorithm (§2) → every record R : PDRun I with IsPDRun I λ μ R (event times 0 = t_0 < … < t_len, forests F_k, active moats A_k ⊇ normal-active moats N_k, obeying the §2 rules at every time); reason: the algorithm is continuous-time; moats and duals are determined by the instance and only the choice among simultaneously tight edges varies, so the statement is made for every run
--   - encoding: ∫_0^∞ … dt of a quantity of A_t → the finite sum over the stages [t_k, t_{k+1}) of the run of the stage length times the quantity; reason: A_t is constant on each stage and empty from the final time on, so the integral is that finite sum (no Bochner-integral junk values)
--   - reading: for fixed constants α, ε we can efficiently find a solution of cost at most … for any collection 𝒮 → for every α ∈ [0, 1], ε > 0 there is one PolyTimeComputable M (fixed before the instance) whose output, on every rational instance, is a forest whose cost satisfies the bound for every run with λ = 2, µ = 10^-12 and every collection 𝒮 of actively connected sets; reason: 𝒮 is not an input: the algorithm of Lemma 15 does not know 𝒮, and the bound must hold for every 𝒮
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 13, Lemma 6 (restated and proved as Lemma 15, p. 52)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_Encoding
import Definitions.Def_PCSFBreach_Main_PrimalDual
import Definitions.Def_PCSFBreach_Main_ActiveConn
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Lemma 6 (p. 13): for fixed `α ∈ [0, 1]`, `ε > 0` one polynomial-time algorithm finds a solution
of cost at most `2 · y(H) + (α + ε) · st(𝒮) − (1 − e^{−α}) · gain(𝒮) + π(Q)` for every collection
`𝒮` of actively connected sets. -/
theorem lemma_6 (α ε : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hε : 0 < ε) :
    ∃ M : Str → Str, PolyTimeComputable M ∧ ∀ J : RatInstance, ∃ F : Finset J.toInstance.Edge,
      M (encInst J) = encEdgeSet J.toInstance F ∧ J.toInstance.IsForest F ∧
      ∀ R : PDRun J.toInstance, IsPDRun J.toInstance 2 (1 / 10 ^ 12) R →
        ∀ 𝒮 : Finset (Finset (Fin J.toInstance.n)), R.IsActConnColl 𝒮 →
          J.toInstance.cost F ≤ 2 * R.yH + (α + ε) * J.toInstance.stColl 𝒮
            - (1 - Real.exp (-α)) * R.gain 𝒮 + J.toInstance.penaltyOf (R.Q 2) := by sorry

end PCSFBreach.Main
