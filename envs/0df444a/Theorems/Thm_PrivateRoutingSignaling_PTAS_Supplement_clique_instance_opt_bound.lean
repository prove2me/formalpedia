-- Prove2me | Theorems.Thm_PrivateRoutingSignaling_PTAS_Supplement_clique_instance_opt_bound
-- name    : PrivateRoutingSignaling.PTAS.Supplement.clique_instance_opt_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:47:36.366736+00:00
-- url     : https://prove2.me/theorems/384c9d64-6598-4a77-a0d6-68d7a1e64560
-- title:
--   Lemma 4.8 — optimum of the CLIQUE-based instance is at most $D^{\mathrm{aux}}(Y)+\lambda_HD^H(Y)+\lambda_H\Delta/4$
-- statement:
--   Let $G$ be a simple graph on $N\ge2$ vertices, and build from it the private signaling instance of §4.4 on $2N$ parallel arcs: the hard state $H$, the designated dual solution $Y$, the auxiliary states $P_\ell$ and $Q_\ell$ ($\ell\in[N]$), a zero-latency dummy state, and the priors $\lambda_H=T\Delta/2$, $\lambda_{P_\ell}=\frac1{4N^2}$, $\lambda_{Q_\ell}=\frac1{2N}$, $\lambda_0=\frac12-\frac1{4N}-\lambda_H$, where $\Delta=\frac1{4N^3}$ and $T=\frac1{2^{12}N^4}$. Let $\mathrm{OPT}$ be the minimum social cost over all exactly incentive-compatible signaling schemes with this prior. Then
--
--   $$
--   \mathrm{OPT}\ \le\ D^{\mathrm{aux}}(Y)+\lambda_HD^H(Y)+\frac{\lambda_H\Delta}4,
--   \qquad D^{\mathrm{aux}}(y)=\frac1{4N^2}\sum_{\ell=1}^ND^{P_\ell}(y)+\frac1{2N}\sum_{\ell=1}^ND^{Q_\ell}(y).
--   $$
--
--   Combined with Lemma 2.1, this upper bound makes the optimum of the signaling instance track $D^H(Y)$, and hence the clique number of $G$, up to an inverse-polynomial error; it is the main step of Theorem 4.9.
--
--   **Formalization Note** $\mathrm{OPT}$ is the base mission's extended-real infimum of social cost over all Borel probability schemes with the prior that satisfy the exact IC constraints; the bound is stated in $\overline{\mathbb R}$. The instance is the explicit constructor of the CliqueInstance definition.
--
--   Differences from the source:
--   - encoding: "the private signaling instance constructed above" with arcs indexed by [n] = [2N] and an unordered list of states → the explicit constructor with arcs 0, …, 2N−1 and states ordered H, P_1, …, P_N, Q_1, …, Q_N, dummy; reason: a fixed indexing of the same instance
--   - encoding: OPT, a minimum over exactly IC schemes → the base mission's extended-real infimum over all exactly IC Borel probability schemes with the prior; reason: the published benchmark; the bound is a real number cast to the extended reals
-- source:
--   Yu Cheng, Tianle Jiang, The Complexity of Private Signaling in Nonatomic Routing Games, STOC 2027 submission #439 (October 2026), Lemma 4.8, p. 23 (PDF p. 23); proof pp. 23–24; construction pp. 16–23 (N ≥ 2 from the proof of Theorem 4.2, p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf; SHA-256 766b4afa05d6c7c4c106ed83a73221ca4d951eeca5cce863930177ed26fd4e61

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_CliqueInstance

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS.Supplement

open PrivateRoutingSignaling.PTAS

/-- Lemma 4.8 (Cheng–Jiang, STOC 2027 submission #439, p. 23; proof pp. 23–24). For the
instance of §4.4 built from a graph on `N ≥ 2` vertices,
`OPT ≤ D^aux(Y) + λ_H D^H(Y) + λ_H Δ/4`, with `OPT` the exact-IC optimum over all Borel schemes. -/
theorem clique_instance_opt_bound (N : ℕ) (hN : 2 ≤ N) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] :
    optimum (Clique.inst N G) ≤
      ((Clique.daux N G (Clique.Y N G) +
        Clique.priorH N * dualValue (Clique.inst N G) (Clique.hState N) (Clique.Y N G) +
        Clique.priorH N * Clique.gap N / 4 : ℝ) : EReal) := by sorry

end PrivateRoutingSignaling.PTAS.Supplement
