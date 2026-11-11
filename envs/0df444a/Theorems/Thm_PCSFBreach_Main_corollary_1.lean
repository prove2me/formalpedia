-- Prove2me | Theorems.Thm_PCSFBreach_Main_corollary_1
-- name    : PCSFBreach.Main.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:59.527865+00:00
-- url     : https://prove2.me/theorems/2aab653d-a34d-4ce8-9985-94db6ef9694d
-- title:
--   Corollary 1 — with g = 10⁻³: if st(𝒮) ≤ 2L and gain(𝒮) − st(𝒮) ≥ gL, a solution of cost ≤ 2y(H) + π(Q) − (g²/32)L
-- statement:
--   Let $g=10^{-3}$. There is one polynomial-time computable function $M$ such that for every PCSF instance $J$ with nonnegative rational data, $M$ maps the code of $J$ to the code of a forest $F$ of $J$ with the following property. For every run of the primal-dual algorithm with $\lambda=2$, $\mu=10^{-12}$ on $J$ and every $L>0$: if some collection $\mathcal S$ of actively connected sets satisfies $\mathrm{st}(\mathcal S)\le 2L$ and $\mathrm{gain}(\mathcal S)-\mathrm{st}(\mathcal S)\ge gL$, then
--   $$\mathrm{cost}(F)\le 2y(H)+\pi(Q)-\frac{g^2}{32}L .$$
--
--   This is the form in which the contraction algorithm enters the case analysis of Theorem 2.
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: a polynomial-time algorithm on (G, c, D, π) → one function M on binary strings with PolyTimeComputable M (published QAlgorithms_ClassicalStringComputability: Mathlib multi-stack Turing machine, time polynomial in the input length), fixed before the instance, mapping the binary code encInst J of every instance J with nonnegative rational costs and penalties to the characteristic vector encEdgeSet of its output edge set; reason: bit model; Appendix B (p. 47) assumes rational input data; the vertex count n is coded in unary (the input graph G = (V, E) lists its vertices) and every other number in binary, so the time bound is polynomial in |V| plus the bit length of the data; strings that code no instance are unconstrained
--   - encoding: a solution → an edge set F that is a forest of the instance (IsForest: no loop, no edge joining two vertices already connected by the other edges of F); reason: p. 1: a feasible solution is any forest F ⊆ E
--   - encoding: the run of §4–§8 on a fresh instance (λ = 2, µ = 10^-12, p. 12) → every run with IsPDRun I 2 (1/10^12) R; reason: the section's standing parameters, kept as printed
--   - encoding: the run of the primal-dual algorithm (§2) → every record R : PDRun I with IsPDRun I λ μ R (event times 0 = t_0 < … < t_len, forests F_k, active moats A_k ⊇ normal-active moats N_k, obeying the §2 rules at every time); reason: the algorithm is continuous-time; moats and duals are determined by the instance and only the choice among simultaneously tight edges varies, so the statement is made for every run
--   - encoding: ∫_0^∞ … dt of a quantity of A_t → the finite sum over the stages [t_k, t_{k+1}) of the run of the stage length times the quantity; reason: A_t is constant on each stage and empty from the final time on, so the integral is that finite sum (no Bochner-integral junk values)
--   - reading: fix g, let L > 0; suppose there exists 𝒮 …; then we can efficiently construct a solution → one PolyTimeComputable M fixed before L, the instance and the run; its output satisfies the bound for every L > 0 and every run for which such an 𝒮 exists; reason: the construction (Lemma 15 with α = g/4, ε = g²/32, proof of Corollary 2) does not depend on L or 𝒮; this is the stronger reading
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 13, Corollary 1 (restated and proved as Corollary 2, pp. 52–53)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_Encoding
import Definitions.Def_PCSFBreach_Main_PrimalDual
import Definitions.Def_PCSFBreach_Main_ActiveConn
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Corollary 1 (p. 13), `g = 1/10³`: one polynomial-time algorithm whose solution costs at most
`2y(H) + π(Q) − (g²/32) L` whenever `L > 0` and some collection `𝒮` of actively connected sets has
`st(𝒮) ≤ 2L` and `gain(𝒮) − st(𝒮) ≥ gL`. -/
theorem corollary_1 :
    ∃ M : Str → Str, PolyTimeComputable M ∧ ∀ J : RatInstance, ∃ F : Finset J.toInstance.Edge,
      M (encInst J) = encEdgeSet J.toInstance F ∧ J.toInstance.IsForest F ∧
      ∀ R : PDRun J.toInstance, IsPDRun J.toInstance 2 (1 / 10 ^ 12) R → ∀ L : ℝ, 0 < L →
        (∃ 𝒮 : Finset (Finset (Fin J.toInstance.n)), R.IsActConnColl 𝒮 ∧
            J.toInstance.stColl 𝒮 ≤ 2 * L ∧ R.gain 𝒮 - J.toInstance.stColl 𝒮 ≥ (1 / 10 ^ 3) * L) →
          J.toInstance.cost F ≤ 2 * R.yH + J.toInstance.penaltyOf (R.Q 2) - ((1 / 10 ^ 3) ^ 2 / 32) * L := by sorry

end PCSFBreach.Main
