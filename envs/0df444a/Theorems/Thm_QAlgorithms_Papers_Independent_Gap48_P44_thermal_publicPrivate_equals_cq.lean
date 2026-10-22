-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_thermal_publicPrivate_equals_cq
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.thermal_publicPrivate_equals_cq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:46:17.738161+00:00
-- url     : https://prove2.me/theorems/eabf09f6-76b6-45e0-8d74-3473c9441a68
-- title:
--   Thermal coherent public/private and CQ families coincide
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. Fix $0\le\eta\le1$ and finite $N_S,N_B\ge0$. Write $a=g_b(\eta N_S+(1-\eta)N_B)$, $b_\lambda=g_b(\eta\lambda N_S+(1-\eta)N_B)$, $h=g_b((1-\eta)N_B)$, and $e_\lambda=g_b([D+\lambda(1-\eta)N_S-(1-\eta)N_B-1]/2)+g_b([D-\lambda(1-\eta)N_S+(1-\eta)N_B-1]/2)$, where $D=\sqrt{[\lambda(1+\eta)N_S+(1-\eta)N_B+1]^2-4\eta\lambda N_S(\lambda N_S+1)}$ is nonnegative. Let $A$ be the union over $\lambda\in[0,1]$ of nonnegative pairs $(u,v)$ with $v\le b_\lambda-e_\lambda$ and $u+v\le a-e_\lambda$. Then
--
--   $$\{(u,v)\in A:u+v\le a-h\}=A.$$
--
--   The left side is the coherent-ensemble private inner family at zero key rate, relabeled as public/private rates; the right side is the displayed CQ inner family. The complementary entropy includes the thermal purifier, and this equality does not assert equality of operational capacities.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 15, §IV B: coherent-ensemble public/private and CQ coincidence

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.15, Section IV B: the displayed coherent-ensemble public/private
family at S=0 equals the displayed CQ family, after relabeling (R,P)=(C,Q).
Only the explicit inner families are compared, with both modes of the true
complement in (80); this is not equality of operational channel capacities. -/
theorem thermal_publicPrivate_equals_cq (eta budget noise : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hbudget : 0 ≤ budget) (hnoise : 0 ≤ noise) :
    let output := thermalEntropy (eta * budget + (1 - eta) * noise)
    let conditional := fun share => thermalEntropy (eta * share * budget + (1 - eta) * noise)
    let environment := fun share => thermalEnvironment eta share budget noise
    {r ∈ cqFamily output conditional environment |
      r.1 + r.2 ≤ output - thermalEntropy ((1 - eta) * noise)} =
      cqFamily output conditional environment := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
