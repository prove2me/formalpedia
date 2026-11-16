-- Prove2me | Theorems.Thm_UCalibDirichlet_Supplement_theorem_E_6
-- name    : UCalibDirichlet.Supplement.theorem_E_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:15:38.148481+00:00
-- url     : https://prove2.me/theorems/576644ed-a4fb-4169-91a0-86b328b051de
-- title:
--   Theorem E.6 — variance–curvature tradeoff: $R^*_F(T)\ge\frac{\kappa\eta(1-\eta)}2\log\big(1+\frac{T\delta^2}{\pi^2\eta(1-\eta)}\big)$
-- statement:
--   Fix $0<\eta<1/2$. Let $F:[0,1]\to\mathbb R$ and let $\ell$ be a binary proper loss (finite Bayes risk) with Bayes risk $-F$. Let $\delta>0$, $\kappa\ge 0$ and $p_0$ be such that $I=[p_0-\delta,p_0+\delta]\subseteq[\eta,1-\eta]$, and suppose $p\mapsto F(p)-\kappa p^2/2$ is convex on $I$ ($F$ is $\kappa$-strongly convex on $I$). Then:
--
--   1. for every $T\ge 1$,
--   $$R^*_F(T)\ \ge\ \frac{\kappa\,\eta(1-\eta)}{2}\,\log\Big(1+\frac{T\delta^2}{\pi^2\eta(1-\eta)}\Big);$$
--   2. there is a constant $c>0$ depending only on $\eta$ such that, under the same hypotheses, for every $T\ge 1$,
--   $$R^*_F(T)\ \ge\ c\,\kappa\log(T\delta^2),$$
--   i.e. $R^*_F(T)=\Omega(\kappa\log(T\delta^2))$ for fixed $\eta$.
--
--   Here $R^*_F(T)$ is the minimax regret of the loss $\ell$. The bound comes from label sequences drawn from a mixture of i.i.d. laws, and it can exceed the i.i.d. lower bound $L_F(T)$: for quadratic loss $L_F$ is constant while this bound grows like $\log T$.
--
--   **Formalization Note** Forecasts are points $q=(1-p,p)$ of $\Delta_2$. The paper's remark that, for locally absolutely continuous $F'$, the convexity assumption is equivalent to $F''\ge\kappa$ a.e. on $I$ restates the hypothesis and is not a separate claim.
--
--   Differences from the source:
--   - reading: R*_F for a potential F (the theorem's sentence names no loss) → every proper loss ℓ with finite Bayes risk and bayesPot ℓ = F on Δ₂; reason: the setting of Proposition E.5 (p.44), which the proof applies: a proper loss of Bayes risk −F
--   - generalization: F ∈ C[0,1] (Proposition E.5's setting) → no continuity hypothesis on F; reason: the proof (minimax ≥ expected regret against a mixture of i.i.d. laws, propriety, Jensen for the finitely supported p̂_T, strong convexity on I) never uses continuity, and continuous F are a special case
--   - encoding: F convex (Proposition E.5) → no separate convexity hypothesis; reason: the potential of a proper loss is convex on the simplex, so the hypothesis excludes nothing (trap 36)
--   - reading: In particular, fixing η, R*_F(T) = Ω(κ log(Tδ²)) (73) → ∃ c > 0 after η and before F, ℓ, p₀, δ, κ; bound for every T ≥ 1; reason: the constant may depend only on the fixed η; a threshold in T could not be uniform in δ, and for Tδ² ≤ 1 the right side is ≤ 0
--   - encoding: binary forecast p ∈ [0,1], R*_F(T) → q ∈ Δ₂ with p = q 1; minimaxRegret ℓ T; reason: the base model at K = 2
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem E.6, displays (72)–(73), p.45 (with Proposition E.5, p.44)

import Mathlib
import Definitions.Def_UCalibDirichlet_IsProperLoss
import Definitions.Def_UCalibDirichlet_HasFiniteBayesRisk
import Definitions.Def_UCalibDirichlet_bayesPot
import Definitions.Def_UCalibDirichlet_Supplement_minimaxRegret

namespace UCalibDirichlet.Supplement

/-- **Theorem E.6 (Variance–curvature tradeoff).** Frongillo, Luo, Mehta & Schneider (manuscript,
STOC 2027 submission), Theorem E.6, displays (72)–(73), p.45: "Fix `0 < η < 1/2`. Let
`I = [p₀ − δ, p₀ + δ] ⊂ [η, 1 − η]`, `δ > 0`, and suppose `F(p) − κp²/2` is convex on `I` (i.e., `F`
is `κ`-strongly convex on `I`), for some `κ ≥ 0`. Then
`R*_F(T) ≥ (κη(1 − η)/2) log(1 + Tδ²/(π²η(1 − η)))`. (72) If `F′` is locally absolutely continuous,
the convexity assumption is equivalently `F″ ≥ κ` a.e. on `I`. In particular, fixing `η`, we have
`R*_F(T) = Ω(κ log(Tδ²))`. (73)"

Fix `0 < η < 1/2`. Let `F : [0, 1] → ℝ` and `ℓ` a binary proper loss with finite Bayes
risk whose potential is `F` (Bayes risk `−F`). Let `δ > 0`, `κ ≥ 0` and `p₀` with
`[p₀ − δ, p₀ + δ] ⊆ [η, 1 − η]`, and suppose `p ↦ F(p) − κp²/2` is convex on `[p₀ − δ, p₀ + δ]`. Then:
1. for every `T ≥ 1`, `R*(T) ≥ (κη(1 − η)/2) log(1 + Tδ²/(π²η(1 − η)))`;
2. there is `c > 0` depending only on `η` such that, under the same hypotheses,
   `R*(T) ≥ c κ log(Tδ²)` for every `T ≥ 1`.

**Formalization Note.** The proof applies Proposition E.5 (p.44), stated for `F ∈ C[0, 1]` convex
with a proper loss of Bayes risk `−F`. Continuity is not assumed here: the argument (minimax ≥
regret against a mixture of i.i.d. laws, propriety, and Jensen for the finitely supported `p̂_T`)
holds for every convex `F` on `[0, 1]`, so the statement contains the source's. Convexity of `F` is
not a separate hypothesis: it follows from propriety (`F` is the potential of a proper loss). `Ω` in (73) "fixing `η`" is a
constant depending only on `η`, quantified after `η` and before everything else, and the bound is
stated for every `T ≥ 1`. The sentence on `F″ ≥ κ` glosses the hypothesis and is not a separate
claim. Forecasts are `q : Fin 2 → ℝ` with `p = q 1`. -/
theorem theorem_E_6 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    (∀ F : ℝ → ℝ,
      ∀ ℓ : (Fin 2 → ℝ) → Fin 2 → EReal, IsProperLoss ℓ → HasFiniteBayesRisk ℓ →
      (∀ q ∈ stdSimplex ℝ (Fin 2), bayesPot ℓ q = F (q 1)) →
      ∀ p₀ δ κ : ℝ, 0 < δ → η ≤ p₀ - δ → p₀ + δ ≤ 1 - η → 0 ≤ κ →
      ConvexOn ℝ (Set.Icc (p₀ - δ) (p₀ + δ)) (fun p => F p - κ * p ^ 2 / 2) →
      ∀ T : ℕ, 1 ≤ T →
        ((κ * η * (1 - η) / 2 * Real.log (1 + T * δ ^ 2 / (Real.pi ^ 2 * η * (1 - η))) : ℝ) :
          EReal) ≤ minimaxRegret ℓ T) ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ F : ℝ → ℝ,
      ∀ ℓ : (Fin 2 → ℝ) → Fin 2 → EReal, IsProperLoss ℓ → HasFiniteBayesRisk ℓ →
      (∀ q ∈ stdSimplex ℝ (Fin 2), bayesPot ℓ q = F (q 1)) →
      ∀ p₀ δ κ : ℝ, 0 < δ → η ≤ p₀ - δ → p₀ + δ ≤ 1 - η → 0 ≤ κ →
      ConvexOn ℝ (Set.Icc (p₀ - δ) (p₀ + δ)) (fun p => F p - κ * p ^ 2 / 2) →
      ∀ T : ℕ, 1 ≤ T →
        ((c * κ * Real.log (T * δ ^ 2) : ℝ) : EReal) ≤ minimaxRegret ℓ T := by sorry

end UCalibDirichlet.Supplement
