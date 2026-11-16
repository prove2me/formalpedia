-- Prove2me | Theorems.Thm_PrivateRoutingSignaling_PTAS_Supplement_continuous_instance_bounds
-- name    : PrivateRoutingSignaling.PTAS.Supplement.continuous_instance_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:51:25.505191+00:00
-- url     : https://prove2.me/theorems/210c1ac4-ddae-43fa-aeee-86b87600a93c
-- title:
--   Lemma 6.7 — two-sided bounds for the continuous short-path MAX-CUT instance
-- statement:
--   Let $G$ be a cubic graph on $N>0$ vertices and $0<\delta\le1$. Set $\lambda_H=\frac\delta{256}$ and $\eta=\lambda_H\delta$, and build the continuous private signaling instance of §6.3: the two-arc gadget network, the smoothed hard state and states $P_U$ of Remark 6.6, the states $Q_i$, a zero-latency dummy state, and priors $\lambda_H$, $\frac1{8N}$ on each $P_U$, $\frac1{2N}$ on each $Q_i$ and $\frac14-\lambda_H$ on the dummy. Let $\widetilde{\mathrm{OPT}}$ be the minimum social cost over its exactly incentive-compatible signaling schemes. Then
--
--   $$
--   \widetilde{\mathrm{OPT}}\le\frac{1+\eta}8-\lambda_H\frac{\mathrm{MaxCut}(G)}{4N},
--   $$
--
--   and every signaling scheme $\varphi$ satisfying the $\varepsilon$-relaxed IC constraints, for a tolerance $\varepsilon\ge0$, has
--
--   $$
--   \mathrm{SC}(\varphi)\ge\frac{1-\eta}8-\lambda_H\Bigl(\frac{\mathrm{MaxCut}(G)}{4N}+2\eta\Bigr)-\varepsilon.
--   $$
--
--   With $\delta$ the gap of cubic MAX-CUT normalized by $4N$, the two bounds separate the two MAX-CUT cases by a constant, which gives Theorem 6.8.
--
--   **Formalization Note** $\widetilde{\mathrm{OPT}}$ is the base mission's extended-real exact-IC optimum over Borel schemes, and the upper bound is a real number cast to the extended reals. Schemes in the second part are arbitrary Borel probability measures with the prior as state marginal. $\mathrm{MaxCut}(G)$ is the published `MISInducedMinor.maxCut`.
--
--   Differences from the source:
--   - generalization: δ = C′_1 − C′_2 for the gap constants of cubic MAX-CUT normalized by 4N → any 0 < δ ≤ 1; reason: the proof (Remark 6.6, duality and Lemma 2.1) uses only 0 < δ ≤ 1, which gives λ_H ≤ (1 − η)/32 and η ≤ 1/2, and 0 ≤ C′_2 < C′_1 ≤ 1 gives such a δ
--   - reading: the ε-relaxed IC constraints with an unrestricted ε → ε ≥ 0; reason: ε is a tolerance (§2.3, p. 8) and the bound is derived from Lemma 2.1, which needs ε ≥ 0
--   - encoding: ÕPT, the optimal social cost of this instance → the base mission's extended-real infimum over all exactly IC Borel probability schemes with the prior; reason: the published benchmark
-- source:
--   Yu Cheng, Tianle Jiang, The Complexity of Private Signaling in Nonatomic Routing Games, STOC 2027 submission #439 (October 2026), Lemma 6.7, p. 37 (PDF p. 37); construction §§6.1–6.3 pp. 31–37, Remark 6.6 pp. 36–37; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf; SHA-256 766b4afa05d6c7c4c106ed83a73221ca4d951eeca5cce863930177ed26fd4e61

import Mathlib
import Definitions.Def_MISInducedMinor_maxCut
import Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_ShortPathInstance

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS.Supplement

open PrivateRoutingSignaling.PTAS

/-- Lemma 6.7 (Cheng–Jiang, STOC 2027 submission #439, p. 37). For a cubic graph on `N > 0`
vertices and a gap `0 < δ ≤ 1`, with `λ_H = δ/256` and `η = λ_H δ`, the continuous instance of
§6.3 has `ÕPT ≤ (1+η)/8 − λ_H MaxCut(G)/(4N)`, and every scheme satisfying the `ε`-relaxed IC
constraints (`ε ≥ 0`) has `SC(φ) ≥ (1−η)/8 − λ_H (MaxCut(G)/(4N) + 2η) − ε`. -/
theorem continuous_instance_bounds (N : ℕ) (hN : 0 < N) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    optimum (ShortPath.inst N G (δ / 256 * δ) (δ / 256)) ≤
        (((1 + δ / 256 * δ) / 8 -
          δ / 256 * (((MISInducedMinor.maxCut G : ℕ) : ℝ) / (4 * N)) : ℝ) : EReal) ∧
      ∀ ε : ℝ, 0 ≤ ε → ∀ φ : Scheme (ShortPath.inst N G (δ / 256 * δ) (δ / 256)),
        IsScheme (ShortPath.inst N G (δ / 256 * δ) (δ / 256)) φ →
        Obedient (ShortPath.inst N G (δ / 256 * δ) (δ / 256)) ε φ →
        (1 - δ / 256 * δ) / 8 -
            δ / 256 * (((MISInducedMinor.maxCut G : ℕ) : ℝ) / (4 * N) + 2 * (δ / 256 * δ)) - ε ≤
          socialCost (ShortPath.inst N G (δ / 256 * δ) (δ / 256)) φ := by sorry

end PrivateRoutingSignaling.PTAS.Supplement
