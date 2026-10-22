-- Prove2me | Theorems.Thm_RiskPostpone_Threshold_tailMean_strictMono
-- name    : RiskPostpone.Threshold.tailMean_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:26.336279+00:00
-- url     : https://prove2.me/theorems/be6b8ae0-6df4-4d27-99f9-8b88a35b4f87
-- title:
--   Proofs of Propositions 2 and 3, pp. ec4, ec8 — g(η) is strictly increasing and continuous, g(1) = µ, g(0+) = l
-- statement:
--   Let the yield $\xi$ have an atomless law with full support on $[l,u]$, $0\le l<u\le1$, and let
--   $$
--   g(\eta)=\frac1\eta\int_l^{G^{-1}(\eta)}\xi\,dG(\xi),\qquad\eta\in(0,1],
--   $$
--   be the mean of the lower $\eta$-tail of the yield. Then $g$ is strictly increasing and continuous on $(0,1]$, $g(1)=\mu$, and $g(\eta)\to l$ as $\eta\to0^+$.
--
--   These properties give, for every cost ratio $c/p_0\in(l,\mu]$, a unique root of $g(\eta)=c/p_0$, which is the risk-aversion threshold of both pricing schemes.
--
--   **Formalization Note** The paper computes $g'(\eta)>0$ using a density; with only an atomless law, strict monotonicity and continuity are stated instead. The paper's "$g(0)=G^{-1}(0)=l$" is the right limit at $0$, since $g$ is not defined at $\eta=0$.
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), p. ec4 (PDF 37), proof of Proposition 2, and p. ec8 (PDF 41), proof of Proposition 3, definition and monotonicity of g(η)

import Mathlib
import Definitions.Def_RiskPostpone_Threshold_Setting

open MeasureTheory Set Filter Topology

namespace RiskPostpone.Threshold

/-- Proof of Proposition 2 (p. ec4): the tail mean `g(η) = (1/η) ∫_l^{G⁻¹(η)} ξ dG(ξ)` is
strictly increasing and continuous on `(0,1]`, `g(1) = µ`, and `g(η) → l` as `η → 0⁺`. -/
theorem tailMean_strictMono (M : Model) (hM : M.YieldLaw) :
    StrictMonoOn M.tailMean (Ioc 0 1) ∧ ContinuousOn M.tailMean (Ioc 0 1) ∧
    M.tailMean 1 = M.mean ∧ Tendsto M.tailMean (𝓝[>] 0) (𝓝 M.l) := by sorry

end RiskPostpone.Threshold
