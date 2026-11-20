-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_hub_runner_up
-- name    : StableMSR.Recovery.Supplement.hub_runner_up
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T03:15:48.544302+00:00
-- url     : https://prove2.me/theorems/4a164af0-82a9-4764-943a-332da16d0aae
-- title:
--   Lemma C.1 — hub construction and runner-up optimum
-- statement:
--   For a rational finite metric $(Y,d_Y)$, $1\le k\le |Y|$, positive rational $\tau$, and rational $\gamma>1$, form the hub/dummy instance of Appendix C. Let $D=\operatorname{diam}(Y)$, $a=\mathrm{OPT}_k(Y)$, $R_0=1+D+\tau+\tau/(\gamma-1)$, $\delta=\gamma R_0-\tau$, and $K=k+2$. Its prescribed partition $\mathcal O_0$ satisfies
--
--   $$a\le D<R_0,\qquad \operatorname{cost}_d(\mathcal O_0)=R_0,\qquad
--   \min_{\substack{\mathcal Q\text{ exact-}K\\\mathcal Q\ne\mathcal O_0}}\operatorname{cost}_d(\mathcal Q)=\delta+a.$$
--
--   The competing minimum is attained, the constructed distance array is metric, and $\mathcal O_0$ is the unique original optimum. This pins down the entire construction and the exact runner-up value used in the hardness reduction.
--
--   Differences from the source:
--   - encoding: Finite ordered metric input and unordered exact-k partitions → Fin n points, real metric arrays, and finite sets of nonempty disjoint blocks; reason: Input-order relabelling preserves every source instance and partition; base published definitions are reused without extra conditions
--   - encoding: Minimum over different exact-K partitions in the constructed metric → An explicit competitor attaining delta+a, a lower bound for every competitor, and the metric property from the construction preamble; reason: This states the minimum with attainment rather than a possibly default real infimum; all parameters remain those of Appendix C
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma C.1, p. 24; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Supplement_Hub

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

theorem hub_runner_up {n k : ℕ} (d : Point n → Point n → ℚ) (γ τ : ℚ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray (fun x y => (d x y : ℝ)))
    (hγ : 1 < γ) (hτ : 0 < τ) :
    let dr := fun x y => (d x y : ℝ)
    let a := optimumValue dr k
    let dp := hubDistance dr k γ τ
    let O₀ := suppliedPartition n k
    a ≤ diameter dr Finset.univ ∧ diameter dr Finset.univ < hubRadius dr γ τ ∧
    IsMetricArray dp ∧ cost dp O₀ = hubRadius dr γ τ ∧
    (∃ Q, Feasible Finset.univ (k + 2) Q ∧ Q ≠ O₀ ∧ cost dp Q = dummyDistance dr γ τ + a) ∧
    (∀ Q, Feasible Finset.univ (k + 2) Q → Q ≠ O₀ → dummyDistance dr γ τ + a ≤ cost dp Q) ∧
    UniqueOptimal dp Finset.univ (k + 2) O₀ := by sorry

end StableMSR.Recovery.Supplement
