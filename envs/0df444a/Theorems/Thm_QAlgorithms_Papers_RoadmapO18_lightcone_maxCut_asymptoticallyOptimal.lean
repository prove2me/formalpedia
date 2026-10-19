-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapO18_lightcone_maxCut_asymptoticallyOptimal
-- name    : QAlgorithms.Papers.RoadmapO18.lightcone_maxCut_asymptoticallyOptimal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:05:26.844018+00:00
-- url     : https://prove2.me/theorems/e5c77763-dbff-48e2-bfde-80a86898f4e6
-- title:
--   Asymptotically optimal 0-local lightcone-ZY1 MaxCut certificate
-- statement:
--   Let $(G_j)$ be any family of finite nonempty connected undirected unweighted simple cubic graphs, with $N_j\to\infty$. For each graph, choose a root and construct the one-round lightcone-ZY schedule $S_j$ by recursive BFS, resolving unspecified ties by vertex labels. Each schedule starts in $|+\rangle^{\otimes N_j}$ and uses one gate $e^{-i\theta Z_iY_j/2}$ per directed edge, with a common real angle. Let $L_0(G,S;\theta)$ be the expected cut computed by the isolated-boundary 0-local prescription, $C_{\max}(G)$ the attained maximum cut, $\alpha_0(G,S)=\max_\theta L_0(G,S;\theta)/C_{\max}(G)$, and $b_0(G,S)=\max_\theta L_0(G,S;\theta)/|E(G)|$. Let $N_+(S)$ count the zero-in-degree vertices and put
--
--   $$k_j=\frac23+\frac{4N_+(S_j)}{3N_j},\qquad B(k)=\max_{0\le\theta\le\pi/2}\frac12[1+(1-k)\sin\theta+k\cos\theta\sin\theta].$$
--
--   For every $\varepsilon>0$, there is $j_0$ such that for all $j\ge j_0$,
--
--   $$\alpha_0(G_j,S_j)\ge B(k_j)-\varepsilon,\qquad |b_0(G_j,S_j)-B(k_j)|\le\varepsilon,$$
--
--   and every arbitrary one-round orientation and gate order $S$ on $G_j$ with $N_+(S)=N_+(S_j)$ satisfies
--
--   $$b_0(G_j,S)\le B(k_j)+\varepsilon.$$
--
--   Thus the lightcone schedule attains the asymptotically optimal edge-count certificate at its source count. The pointwise guarantee gives the corresponding worst-case guarantee over graph classes. Source density need not converge. Optimality concerns this certificate; it does not identify the full-circuit ratio with the certificate.
-- source:
--   Performance guarantees of light-cone variational quantum algorithms for the maximum cut problem, arXiv:2504.12896v4, Theorem 1, equation (7); proof pp.20–22, PDF p. 5. https://arxiv.org/abs/2504.12896v4 . PDF SHA-256: e2e106812bceec60b4fd6653d890862bca316d6c1591b3781c75c7be0067626c.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ZYLocalCertificates
import Definitions.Def_QAlgorithms_Papers_RoadmapO18_Model
set_option autoImplicit false

noncomputable section

open Filter

namespace QAlgorithms.Papers.RoadmapO18

open QAlgorithms QAlgorithms.ZY

attribute [local instance] Classical.propDecidable







/-- arXiv:2504.12896v4, PDF p.5 (7), repeated p.22 (D7), proof pp.20--22.
For growing connected cubic graphs, the computed lightcone-ZY1 ansatz attains the
asymptotically optimal edge-count certificate at its source count. Its 0-local
MaxCut ratio is at least this bound. Competing orientations and orders are arbitrary
but have the same source count (the proof's final paragraph, p.22).
No convergence of source density is assumed, and no finite-graph equality with (7),
full-circuit approximation ratio, or per-shot success probability is asserted. -/
theorem lightcone_maxCut_asymptoticallyOptimal
    (N : ℕ → ℕ) (G : (j : ℕ) → SimpleGraph (Fin (N j)))
    (connected : ∀ j, (G j).Connected) (nonempty : ∀ j, 0 < N j)
    (cubic : ∀ j v, (Finset.univ.filter fun u => (G j).Adj v u).card = 3)
    (root : (j : ℕ) → Fin (N j)) (grows : Tendsto N atTop atTop) :
    ∀ eps : ℝ, 0 < eps → ∃ j0 : ℕ, ∀ j ≥ j0,
      let A := sourceAnsatz (G j) (connected j) (nonempty j) (cubic j) (root j)
      let k := sourceDensityCoefficient (N j) (sourceCount A.orientation) (nonempty j)
      let h := (cubic_domains A.G A.connected A.nonempty A.cubic A.orientation A.sequence).2
      scalarEnvelope k - eps ≤
        @localApproximationRatio A.N A.G (Classical.decRel _) A.orientation
          A.sequence A.positiveCut ∧
      |edgeCountCertificate A.sequence h - scalarEnvelope k| ≤ eps ∧
      ∀ (O : Orientation (G j)) (S : GateSequence O),
        sourceCount O = sourceCount A.orientation →
        edgeCountCertificate S
          ((cubic_domains (G j) (connected j) (nonempty j) (cubic j) O S).2) ≤
            scalarEnvelope k + eps := by sorry

end QAlgorithms.Papers.RoadmapO18
