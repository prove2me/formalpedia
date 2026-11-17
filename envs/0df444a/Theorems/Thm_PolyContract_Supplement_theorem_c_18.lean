-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_c_18
-- name    : PolyContract.Supplement.theorem_c_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:06:09.357563+00:00
-- url     : https://prove2.me/theorems/9df9b058-0ecc-494b-a829-7f7537392722
-- title:
--   Theorem C.18 — the gap of level $k+1$ is at least $\varepsilon_0$ on the transition
-- statement:
--   Let $\mu^{\mathrm{in}}\in\mathcal F$ have length at least $k+2$, build the levels of the comb gadget by the parameter rule, let $k\ge0$ and $e_t,e_l\in E_k$. Assume the hypotheses (W1)–(W6) of Lemma C.15 at each of the steps $0\to1,\dots,k\to k+1$, and (T1)–(T3) at the step $k\to k+1$. Then
--   $$L_{k+1}(\alpha)-r(\xi^{(k+1)}(\alpha))\ \ge\ \varepsilon_0=\tfrac1{30}\qquad\text{for every }\alpha\in[R^{(k)}_1,\,R_0+\mu_{k+1}].$$
--
--   This is the transition theorem: between the two windows of level $k+1$, where the new element crosses the whole old structure, the gap stays bounded away from zero.
--
--   Differences from the source:
--   - reading: Let k ≥ 0 (levels of Definition C.11 from µ^in ∈ F) → µ^in ∈ F of length at least k + 2; reason: the step k → k + 1 uses µ_{k+1} = δµ^in_{k+2}, defined only for that length
--   - encoding: the levels, marginals and reward of Definitions C.11–C.12 → one ambient element type; marginals at a chosen full-plane best response; r(ξ^{(k+1)}) the published full-plane reward; reason: the full-plane best response exists and is unique (published milestone)
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem C.18, App. C.6.3, p.64 (PDF p.65)

import Mathlib
import Definitions.Def_PolyContract_IsComb
import Definitions.Def_PolyContract_Supplement_HypC15

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem C.18** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, App. C.6.3, p.64): let `k ≥ 0` and `e_t, e_l ∈ E_k`. Assume the hypotheses (W1)–(W6) of
Lemma C.15 at the steps `0 → 1, …, k → k + 1`, and (T1)–(T3). Then the gap
`L_{k+1}(α) − r(ξ^{(k+1)}(α))` of level `k + 1` is at least `ε₀` for every `α` in the transition
`[R₁, R₀ + µ]`, with `R₁ = R^{(k)}_1` and `µ = µ_{k+1}`.

**Formalization Note** The levels are those of Definition C.11 built by the parameter rule of
Definition C.12 from `µ^in ∈ F`; the step `k → k + 1` uses `µ_{k+1} = δ µ^in_{k+2}`, so `µ^in` has
length at least `k + 2`. `r(ξ^{(k+1)})` is the reward of the full-plane best response of `g_{k+1}`. -/
theorem theorem_c_18 (μin : List ℕ) (hμ : PerturbedPow8 μin) (k : ℕ) (hlen : k + 2 ≤ μin.length)
    (et el : CombU) (het : et ∈ Elev k) (hel : el ∈ Elev k) (hW : ∀ i ≤ k, HypC15 μin i)
    (hT1 : HypT1 μin k et el) (hT2 : HypT2 μin k el) (hT3 : HypT3 μin k el) :
    ∀ α ∈ Set.Icc (R1 μin k) (R0 + μs μin (k + 1)), ε0 ≤ gap μin (k + 1) α := by sorry

end PolyContract.Supplement
