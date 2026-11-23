-- Prove2me | Theorems.Thm_WhittleGittins_Retirement_Supplement_theorem2_superprocess
-- name    : WhittleGittins.Retirement.Supplement.theorem2_superprocess
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:48:49.456183+00:00
-- url     : https://prove2.me/theorems/ea50acc9-89c5-4c20-aa5f-172de540da88
-- title:
--   Theorem 2 — superprocesses: with u-optimized F, φᵢ, Mᵢ and M-independent optimal controls, F = F̂ and the index rule attains F (finite and infinite horizon)
-- statement:
--   Consider a superprocess: $N$ projects with states $x_i \in X_i$, nonempty control sets $U_i$, rewards $R_i(x_i, u)$ obeying $k(1-\beta) \le R_i(x_i, u) \le K(1-\beta)$, transition kernels $P_i(\cdot \mid x_i, u)$ and discount $0 \le \beta < 1$. All of $F$, $\varphi_i$ and $M_i$ are the $u$-optimized versions defined in the superprocess model. The theorem asserts that Theorem 1 still holds if, in the continuation regions of the one-project problems, the optimal $u$-decisions are independent of $M$, in both of the following forms.
--
--   1. **Finite horizon.** Let $h_i(x_i, n) \in U_i$ be control maps such that, for every $x_i$, $n$ and every retirement reward $M$ with $M < \varphi_i(x_i, n+1, M)$, the control $h_i(x_i, n+1)$ attains $\sup_u \big[R_i(x_i, u) + \beta\,\mathbb E[\varphi_i(x_i(t+1), n, M) \mid u]\big]$. Suppose also that the value functions $x_i \mapsto \varphi_i(x_i, n, M)$ and $x \mapsto F(x, s, M)$ are measurable. Then for all $x$, $s$, $M$:
--      $$F(x, s, M) = \hat F(x, s, M) = K - \int_M^K \prod_i \frac{\partial \varphi_i(x_i, s_i, m)}{\partial m}\, dm;$$
--      if moreover each $x_i \mapsto h_i(x_i, n)$ is measurable, every measurable index rule (engage an active project of maximal modified index $M_i(x_i, s_i)$ if that maximum exceeds $M$, otherwise retire), operated with the controls $h_i(x_i, s_i)$, earns exactly $F(x, s, M)$; and no feasible measurable Markov policy with a measurable control rule earns more than $F(x, s, M)$.
--   2. **Infinite horizon.** Let $F$ and $\varphi_i$ be bounded measurable solutions of $F = \max(M, \max_i \sup_u L_{iu}F)$ and of (22), $\varphi_i = \max(M, \sup_u L_{iu}\varphi_i)$, and let $h_i(x_i) \in U_i$ attain $\sup_u L_{iu}\varphi_i(x_i, M)$ whenever $M < \varphi_i(x_i, M)$, for every $M$. With $M_i(x_i) = \inf\{M : \varphi_i(x_i, M) = M\}$, for all $x$ and $M$:
--      $$F(x, M) = K - \int_M^K \prod_i \frac{\partial \varphi_i(x_i, m)}{\partial m}\, dm \qquad (12),$$
--      $F = L_{i, h_i(x_i)} F$ at $(x, M)$ whenever $M_i(x_i) = \max_j M_j(x_j) \ge M$, and $F(x, M) = M$ whenever $\max_j M_j(x_j) \le M$.
--
--   Theorem 2 extends Whittle's retirement formula and the optimality of the index rule from ordinary bandit processes to Gittins's superprocesses, in which each engaged project must also be operated with a chosen procedure. It is a companion result to Theorem 1 and is not used in its proof.
--
--   **Formalization Note** Projects are indexed by `Fin N`; $\partial/\partial m$ is the right derivative; exhausted projects ($s_i = 0$, index $-\infty$ in the paper) are excluded from the index rule. Policies are Markov in $(x, s, M)$: a project choice in `Option (Fin N)` plus a control rule. The two horizons are stated as two conjuncts, each with its own hypotheses. The infinite-horizon index-rule optimality is stated in dynamic-programming form, as in the base mission's published infinite-horizon item.
--
--   Differences from the source:
--   - reading: F, φᵢ, Mᵢ "modified by incorporation of u-optimization" → recursions and value equations with a supremum over u ∈ Uᵢ in each engaged-project term, and Mᵢ the infimal M with φᵢ = M for these φᵢ; reason: this is display (22) and the display after it on p. 148; bound (1) holds uniformly in u, so every supremum is finite
--   - reading: "Theorem 1 still holds" → both the finite-horizon conclusions of Theorem 1 (F = F̂ of (13), the index rule attains F, no policy earns more) and the infinite-horizon conclusions the proof treats ((12) and the index-rule DP equalities), each with its own hypotheses; reason: the proof on p. 148 treats the infinite horizon and says the finite-horizon results follow by the remarks of Section 4
--   - reading: "in the continuation regions … the optimal u-decisions are independent of M" → control maps hᵢ(xᵢ, n) (resp. hᵢ(xᵢ)) attaining the supremum over u at every (xᵢ, n, M) with M < φᵢ(xᵢ, n, M) (resp. M < φᵢ(xᵢ, M)), one map for all M; reason: the proof on p. 149 uses "u takes the value h(xᵢ) which is optimal in the one-project case (for all M, by hypothesis)"; the supremum is not assumed attained in the retirement region
--   - reading: Φ also "modified" → no conclusion about Φ; reason: Theorem 1's statement involves only F, F̂, Mᵢ and the index rule; Φ enters only through Lemma 1, which is not part of Theorem 1
--   - reading: "the maximal reward" and "a policy" → F defined by backward induction (finite horizon) or as the bounded measurable solution of its DP equation (infinite horizon); policies Markov in (x, s, M), a project choice plus a control rule, ties among maximal indices arbitrary, the control of the engaged project fixed to hᵢ; reason: same conventions as the published Theorem 1 and infinite-horizon items of the base mission; a tie-break among optimal controls other than hᵢ need not attain F
--   - encoding: implicit regularity → hᵢ(·, n) measurable (assumed only for the index-rule attainment clause, where the policy value integrates it), Markov kernels jointly measurable in (xᵢ, u), xᵢ ↦ φᵢ(xᵢ, n, M) and x ↦ F(x, s, M) measurable, policies and control rules measurable, Uᵢ nonempty, R jointly measurable; reason: these only exclude cases in which the paper's conditional expectations E[·] or suprema over u are undefined; they hold automatically for countable state spaces with the discrete σ-algebra
--   - encoding: projects 1, …, N, ∂/∂m, Mᵢ(xᵢ, 0) = −∞ → Fin N (0-based), the right derivative, the index rule ranging over active projects only, [NeZero N] for the infinite-horizon maxima; reason: Lean conventions of the base mission; same instances
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), Theorem 2, p. 148 (PDF 6); proof pp. 148–149 (PDF 6–7), (22); Theorem 1, p. 147 (PDF 5); (12), p. 146 (PDF 4); (13), p. 147 (PDF 5)

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess
import Definitions.Def_WhittleGittins_Retirement_Supplement_SuperBanditProcess

namespace WhittleGittins.Retirement.Supplement

open MeasureTheory ProbabilityTheory

/-- Theorem 2 (p. 148): for a superprocess, with `F`, `φᵢ` and `Mᵢ` modified by `u`-optimization,
Theorem 1 still holds if, in the continuation regions of the one-project problems, the optimal
`u`-decisions are independent of `M`.

Finite horizon: if the control maps `hᵢ(xᵢ, n)` are optimal in every one-project continuation
region (for every `M`), and the value functions are measurable in the state, then `F = F̂` of (13),
every measurable index rule with the modified indices and controls `hᵢ` attains `F` (when the maps
`hᵢ(·, n)` are measurable), and no feasible measurable policy with a measurable control rule earns
more.

Infinite horizon: if `F` and `φᵢ` are the bounded measurable solutions of the `u`-optimized
equations and `hᵢ(xᵢ)` is optimal in every one-project continuation region, then
`F(x, M) = K − ∫_M^K ∏ᵢ ∂φᵢ(xᵢ, m)/∂m dm` (12), `F = L_{i,hᵢ(xᵢ)} F` if `Mᵢ = maxⱼ Mⱼ ≥ M`, and
`F = M` if `maxⱼ Mⱼ ≤ M`. -/
theorem theorem2_superprocess {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    {U : Fin N → Type*} [∀ i, MeasurableSpace (U i)] (B : SuperBanditProcess N X U) :
    (∀ h : ∀ i, X i → ℕ → U i, IsMIndependentControlFin B h →
      (∀ i n M, Measurable (fun xi => phiU B i xi n M)) →
      (∀ s M, Measurable (fun x => FU B x s M)) →
      ∀ (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ),
        FU B x s M = FhatU B x s M ∧
          ((∀ i n, Measurable (fun xi => h i xi n)) →
            ∀ σ : Policy N X, IsMeasurablePolicy σ → IsIndexRuleU B σ →
              polValueU B σ (indexControl h) x s M = FU B x s M) ∧
          (∀ (σ : Policy N X) (c : ControlRule N X U), IsFeasible σ → IsMeasurablePolicy σ →
            IsMeasurableControl c → polValueU B σ c x s M ≤ FU B x s M)) ∧
    (∀ [NeZero N] (F : (∀ j, X j) → ℝ → ℝ) (φ : ∀ i, X i → ℝ → ℝ) (h : ∀ i, X i → U i),
      IsMProcessValueU B F → (∀ i, IsOneProjectValueU B i (φ i)) →
      IsMIndependentControl B φ h →
      ∀ (x : ∀ j, X j) (M : ℝ),
        F x M = B.K - ∫ m in M..B.K, ∏ i, rderiv (φ i (x i)) m ∧
          (∀ i, (∀ j, indexInf (φ j) (x j) ≤ indexInf (φ i) (x i)) →
            M ≤ indexInf (φ i) (x i) → F x M = LopU B i (h i (x i)) (fun z => F z M) x) ∧
          ((∀ j, indexInf (φ j) (x j) ≤ M) → F x M = M)) := by sorry

end WhittleGittins.Retirement.Supplement
