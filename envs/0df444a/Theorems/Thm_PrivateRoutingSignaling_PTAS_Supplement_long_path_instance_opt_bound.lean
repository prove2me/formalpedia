-- Prove2me | Theorems.Thm_PrivateRoutingSignaling_PTAS_Supplement_long_path_instance_opt_bound
-- name    : PrivateRoutingSignaling.PTAS.Supplement.long_path_instance_opt_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:49:14.637846+00:00
-- url     : https://prove2.me/theorems/f4587da1-3936-41ff-8295-a403ae1db806
-- title:
--   Lemma 5.6 — optimum of the long-path MAX-CUT instance is at most $D^{\mathrm{aux}}(Y)+\lambda_HD^H(Y)+\lambda_H\delta/4$
-- statement:
--   Let $G=(V,E)$ be a simple graph with at least one edge and let $0<\delta\le1$. Build the private signaling instance of §5.3: the gadget network of Figure 2 with paths $V_x$ ($x\in\{0,1\}^V$) and $E_r$ ($r\in\{0,1\}^E$), the hard state $H$, the designated dual solution $Y$ with $Y_{V_x,E_{r(x)}}=1$, the auxiliary states $P$, $Q_{e,0}$, $Q_{e,1}$ ($e\in E$), a zero-latency dummy state, and the priors $\lambda_H=T\delta/2$ with $T=2^{-7}$, $\lambda_P=\frac14$, $\lambda_{Q_{e,b}}=\frac1{4|E|}$, $\lambda_0=\frac14-\lambda_H$. Let $\mathrm{OPT}$ be the minimum social cost over all exactly incentive-compatible signaling schemes. Then
--
--   $$
--   \mathrm{OPT}\ \le\ D^{\mathrm{aux}}(Y)+\lambda_HD^H(Y)+\frac{\lambda_H\delta}4,
--   \qquad D^{\mathrm{aux}}(y)=\frac14D^P(y)+\frac1{4|E|}\sum_{e\in E}\bigl(D^{Q_{e,0}}(y)+D^{Q_{e,1}}(y)\bigr).
--   $$
--
--   With $\delta$ the gap of the NP-hard cubic MAX-CUT problem, this bound and Lemma 2.1 separate the two MAX-CUT cases by a constant, which gives Theorem 5.7.
--
--   **Formalization Note** The gadgets are joined in the index order of the vertices and the lexicographic order of the edges. $\mathrm{OPT}$ is the base mission's extended-real exact-IC optimum over Borel schemes; the bound is a real number cast to the extended reals.
--
--   Differences from the source:
--   - generalization: δ = C_1 − C_2 for the cubic MAX-CUT gap constants of [AK00], applied to the cubic graphs of the reduction → any 0 < δ ≤ 1 and any simple graph with at least one edge; reason: the construction of §5.1 is stated for any graph G, the proof (Lemmas 5.2–5.5 and the computation of Lemma 4.8) uses only 0 < δ ≤ 1, and C_1 > C_2 in [0, 1] gives such a δ
--   - encoding: gadgets "connected sequentially in an arbitrary order" → vertex gadgets in index order and edge gadgets in lexicographic order of (u, v), u < v; reason: one fixed choice of the arbitrary order; e = (u, v) with u < v fixes which of Q_{e,0}, Q_{e,1} is which
--   - encoding: |E| ≥ 1 is not displayed → at least one edge; reason: the hard state uses latency 1/|E| and the priors 1/(4|E|)
--   - encoding: OPT, a minimum over exactly IC schemes → the base mission's extended-real infimum over all exactly IC Borel probability schemes; reason: the published benchmark
-- source:
--   Yu Cheng, Tianle Jiang, The Complexity of Private Signaling in Nonatomic Routing Games, STOC 2027 submission #439 (October 2026), Lemma 5.6, p. 30 (PDF p. 30); construction §§5.1–5.3 pp. 25–30 and Figure 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf; SHA-256 766b4afa05d6c7c4c106ed83a73221ca4d951eeca5cce863930177ed26fd4e61

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_LongPathInstance

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS.Supplement

open PrivateRoutingSignaling.PTAS

/-- Lemma 5.6 (Cheng–Jiang, STOC 2027 submission #439, p. 30). For the long-path instance of
§5.3 built from a graph with at least one edge and a gap `0 < δ ≤ 1`,
`OPT ≤ D^aux(Y) + λ_H D^H(Y) + λ_H δ/4`. -/
theorem long_path_instance_opt_bound (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hE : 0 < LongPath.m N G) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    optimum (LongPath.inst N G δ) ≤
      ((LongPath.daux N G δ (LongPath.Y N G) +
        LongPath.priorH δ * dualValue (LongPath.inst N G δ) (LongPath.hState N G) (LongPath.Y N G) +
        LongPath.priorH δ * δ / 4 : ℝ) : EReal) := by sorry

end PrivateRoutingSignaling.PTAS.Supplement
