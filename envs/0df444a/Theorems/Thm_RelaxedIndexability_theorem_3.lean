-- Prove2me | Theorems.Thm_RelaxedIndexability_theorem_3
-- name    : RelaxedIndexability.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:27.242918+00:00
-- url     : https://prove2.me/theorems/71482a79-15ac-4022-93aa-f038968189b4
-- title:
--   Theorem 3 — relaxed indexability iff the passive-time condition (40), and the closed form (41) of the approximated Whittle index
-- statement:
--   Consider a restless bandit with $N$ arms, arm $n$ having $K_n$ states, a row-stochastic transition matrix $\mathbf P^{(n)}$ with rows $p_0,\dots,p_{K_n-1}$ and rewards $B_n$, and a discount factor $0 < \beta < 1$. For an arm and a belief $\omega$ fixed as a point in the threshold, write $\hat V_{\beta,m}$ for the value of the threshold policy with subsidy $m$, $\hat V_{\beta,m}(\omega; u)$ for the value of taking action $u$ at $\omega$ and following the threshold policy afterwards, and $\hat D_\beta$ for its expected total discounted passive time
--   $$
--   \hat D_{\beta}(\omega_1) = \mathbb E_{\pi_{\beta,m}}\Big[\sum_{t=1}^\infty \beta^{t-1}\,\mathbb 1(u(t)=0)\,\Big|\,\omega(1)=\omega_1\Big],
--   $$
--   which does not depend on $m$. Then:
--
--   1. **(39)** For every arm, every threshold $\omega$ and every initial belief $\omega_1$ in the simplex, $m \mapsto \hat V_{\beta,m}(\omega_1)$ is differentiable at every $m$ and
--   $$
--   \frac{d\hat V_{\beta,m}(\omega_1)}{dm} = \hat D_\beta(\omega_1).
--   $$
--   2. **(40)** The bandit satisfies relaxed indexability (Definition 2) if and only if, for every arm and every belief $\omega$ in the simplex fixed as a point in the threshold,
--   $$
--   \beta\,\omega\big(\hat D_\beta(p_0), \dots, \hat D_\beta(p_{K-1})\big)' \ne 1 + \beta\,\hat D_\beta(\mathcal T^1(\omega)).
--   $$
--   3. **(41)** Under relaxed indexability, for every arm, every belief $\omega$ in the simplex and every subsidy $m$: taking the active and the passive action at $\omega$ (then following the threshold policy with threshold $\omega$) achieve the same value if and only if $m = \hat W(\omega)$, where
--   $$
--   \hat W(\omega) = \frac{\omega B' - \beta g(\omega\mathbf P)\big[I_K + \beta H(\mathbf P)G(\mathbf P)\big]B' + \beta\,\omega H(\mathbf P)G(\mathbf P)B'}{1 + \beta f(\omega\mathbf P) + \beta\big[\beta g(\omega\mathbf P) - \omega\big]H(\mathbf P)F(\mathbf P)}
--   $$
--   with $L(\cdot) = L(\cdot,\omega)$, $f = (1-\beta^{L})/(1-\beta)$, $g(x) = \beta^{L(x)} x\mathbf P^{L(x)}$, $F(\mathbf P) = (f(p_k))_k$, $G(\mathbf P)$ the matrix with rows $g(p_k)$, and $H(\mathbf P) = (I_K - \beta G(\mathbf P))^{-1}$.
--
--   So relaxed indexability can be checked by a finite computation per belief, and the approximated Whittle index used by the index policy has an explicit formula.
--
--   Differences from the source:
--   - encoding: "the passive time is independent of m and denoted by D̂_β(ω₁)" → passiveTime has no m argument; reason: the threshold rule (33) compares ω(t)B′ with ωB′ and does not involve m, so the independence holds by construction.
--   - encoding: D̂_{β,m}(ω₁) = dV̂_{β,m}(ω₁)/dm → HasDerivAt of m ↦ V̂_{β,m}(ω₁) with derivative D̂_β(ω₁) at every m, for every threshold ω and every ω₁ in the simplex; reason: the same statement.
--   - reading: "Ŵ(ω) is given by (41)" → under relaxed indexability, for every m, V̂_{β,m}(ω; u=1) = V̂_{β,m}(ω; u=0) iff m equals the right side of (41); reason: Ŵ(ω) is the unique indifference subsidy of Definition 2 and (37).
--   - reading: L(·,ω) = +∞ in f and g → β^{+∞} = 0, so f = 1/(1−β) and g = 0; reason: β^{+∞} = lim βⁿ = 0, as Algorithm 1 uses.
--   - encoding: a restless bandit of N arms → a family of arms indexed by Fin N, each with its own K, P, B, and a common β; reason: the number M of activated arms does not enter Definition 2 or Theorem 3.
--   - generalization: the standing assumptions P irreducible and aperiodic (p.7) and 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: not used by Theorem 3; the statement for every row-stochastic P and every B contains the source's case.
--   - encoding: V̂ is the expected total discounted reward of π_{β,m} → the limit of the n-horizon expected discounted rewards computed by conditioning on the observations (4); reason: the same quantity, the limit exists for 0 < β < 1.
--   - encoding: D̂ is the expected total discounted passive time under π_{β,m} → the limit of the n-horizon expected discounted passive times (reward 1 passive, 0 active) computed by conditioning on the observations (4); reason: the same quantity, the limit exists for 0 < β < 1.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Theorem 3, pp.22–23; Definition 2, p.22; proof EC.6, p.ec10

import Mathlib
import Definitions.Def_RelaxedIndexability_Arm
import Definitions.Def_RelaxedIndexability_thresholdValue
import Definitions.Def_RelaxedIndexability_passiveTime
import Definitions.Def_RelaxedIndexability_RelaxedIndexable
import Definitions.Def_RelaxedIndexability_approxWhittle

open Matrix

namespace RelaxedIndexability

/-- **Theorem 3** (Liu, *Relaxed Indexability and Index Policy for Partially Observable Restless
Bandits*, arXiv:2107.11939v4, Theorem 3, pp.22–23; proof EC.6, p.ec10). Consider a restless
bandit with arms `arms : Fin N → Arm` and discount factor `β ∈ (0, 1)`.

1. (39) For every arm, every threshold `ω` and every initial belief `ω₁` in the simplex, the
   threshold policy's value `V̂_{β,m}(ω₁)` is differentiable in `m` with derivative the passive time
   `D̂_β(ω₁)` (which does not depend on `m`).
2. (40) The bandit satisfies relaxed indexability iff for every arm and every belief `ω` in the
   simplex fixed as a point in the threshold,
   `βω(D̂_β(p₀), …, D̂_β(p_{K−1}))′ ≠ 1 + βD̂_β(T¹(ω))`.
3. (41) Under relaxed indexability, for every arm, every belief `ω` and every subsidy `m`: the
   active and passive actions at `ω` (threshold `ω`, then the threshold policy) achieve the same
   value iff `m = Ŵ(ω)`, the approximated Whittle index (41).

**Formalization Note.** `V̂` and `D̂` are limits of `n`-horizon expected discounted sums
(`thresholdValue`, `passiveTime`); the passive time carries no `m` argument because the threshold
rule (33) does not involve `m`. -/
theorem theorem_3 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) {N : ℕ} (arms : Fin N → Arm) :
    (∀ n : Fin N, ∀ ω ∈ stdSimplex ℝ (Fin (arms n).K), ∀ ω₁ ∈ stdSimplex ℝ (Fin (arms n).K),
      ∀ m : ℝ,
        HasDerivAt (fun m' => thresholdValue β (arms n).P (arms n).B ω m' ω₁)
          (passiveTime β (arms n).P (arms n).B ω ω₁) m) ∧
    (RelaxedIndexable β arms ↔
      ∀ n : Fin N, ∀ ω ∈ stdSimplex ℝ (Fin (arms n).K),
        β * (ω ⬝ᵥ fun k => passiveTime β (arms n).P (arms n).B ω ((arms n).P k)) ≠
          1 + β * passiveTime β (arms n).P (arms n).B ω (ω ᵥ* (arms n).P)) ∧
    (RelaxedIndexable β arms →
      ∀ n : Fin N, ∀ ω ∈ stdSimplex ℝ (Fin (arms n).K), ∀ m : ℝ,
        (thresholdActionValue β (arms n).P (arms n).B ω m true ω =
            thresholdActionValue β (arms n).P (arms n).B ω m false ω ↔
          m = approxWhittle β (arms n).P (arms n).B ω)) := by sorry

end RelaxedIndexability
