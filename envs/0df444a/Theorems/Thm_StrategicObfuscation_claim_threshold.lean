-- Prove2me | Theorems.Thm_StrategicObfuscation_claim_threshold
-- name    : StrategicObfuscation.claim_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:34.059124+00:00
-- url     : https://prove2.me/theorems/8ebdb485-1657-49c7-997d-643431370d58
-- title:
--   Proof of Proposition 1, Claim, p.27 — the threshold $\bar\sigma_2$ (corrected: needs $e(1,1)>0$, $e(1,0)=0$, $p<1$; (3) iff $\sigma<\bar\sigma_2$)
-- statement:
--   Let $pV>c$ and let $f$ be the function of the Claim. Then $f$ is strictly decreasing on $[0,1]$, and $f(\sigma)>0$ for $\sigma<\bar\sigma_1$.
--
--   Suppose moreover $p<1$, $e(1,1)>0$, $e(1,0)=0$, and that $e(1,\cdot)$ and $\pi$ are continuous. Then:
--
--   1. $\bar\sigma_1<\bar\sigma_2<1$, $f(\bar\sigma_2)=0$, and for $\sigma\in[0,1]$, $f(\sigma)>0$ if and only if $\sigma<\bar\sigma_2$;
--   2. $\bar\sigma_2$ strictly increases in $p$;
--   3. if $\pi(\sigma,\cdot)$ is differentiable at every positive effort, $\bar\sigma_2$ strictly decreases in $g$: for $g<g'$ and an effort selection at $g'$ with $e'(1,0)=0$ and $e'(1,\cdot)$ continuous, $\bar\sigma_2(g')<\bar\sigma_2(g)$.
--
--   The threshold $\bar\sigma_2$ separates the region where uncertified proposals are funded for sure from the region where they are funded at random.
--
--   Differences from the source:
--   - generalization: Assumption 1 with ∂²π/∂σ∂e < 0 for a twice differentiable π → IsDetection: monotonicity plus decreasing differences in σ, strict whenever π(σ,·) separates the two efforts; reason: the C² class satisfies it by integrating the mixed partial, and the paper's own example on p.14, which the strict form excludes, also satisfies it
--   - encoding: e(α, σ) written as a function → a fixed selection E with IsEffort π g E; reason: the argmax in (1) may not be a singleton; every selection is covered and existence of a maximizer stays part of the hypothesis, as in (1)
--   - correction: a threshold σ̄2 ∈ (σ̄1, 1) always exists → location of σ̄2 under p < 1 and e(1,1) > 0; reason: counterexample: π(σ,e) = σ exp(−e), g < 1, pV > c; then e(1,σ) = 0 on [0,1], σ̄1 = 1 and f(1) = 0
--   - correction: a threshold σ̄2 ∈ (σ̄1, 1) always exists → location of σ̄2 under e(1,0) = 0; reason: counterexample: π(σ,e) = ((1+σ)/2) exp(−e), g = 4, V = 2, c = 1, p = 11/20; then e(1,σ) = log(2+2σ) > 0, σ̄1 = 0 and f(0) = −1/16, so f < 0 on [0,1]; the appendix's e(1,σ,g) = 0 for all σ ≤ σ̄1(g) presumes the case σ = 0
--   - correction: (3) holds if and only if σ ≤ σ̄2 → 0 < f(σ) ↔ σ < σ̄2, with f(σ̄2) = 0; reason: (3) is strict and f(σ̄2) = 0, so (3) fails at σ̄2
--   - reading: the paper differentiates e and π in the proof of the Claim → continuity of e(1,·) and joint continuity of π for the location of σ̄2; differentiability of π in e at positive efforts for the strict comparative static in g; reason: the location fails without continuity (π = σ(1/(1+e²) + exp(−e))/2, g = 3 has a jump in e(1,·)); the first two conclusions need none of this
--   - reading: σ̄2 increases in p and decreases in g → strict monotonicity; reason: the proof gives sign ∂σ̄2/∂θ = sign ∂f/∂θ with ∂f/∂θ ≠ 0
--   - reading: σ̄2 is the root of f → σ̄2 is sup{σ ∈ [0,1] : f(σ) > 0}; reason: the two agree when f is continuous, and the conclusion f(σ̄2) = 0 records this
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), proof of Proposition 1, Claim, p.27

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_sigmaBarOne
import Definitions.Def_StrategicObfuscation_sigmaBarTwo

open Set

namespace StrategicObfuscation

/-- **The Claim: the threshold `σ̄2` and its comparative statics (corrected).**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), proof of Proposition 1, Claim, p.27 (PDF p.27).

Let `pV > c`, and let `f` be `gap`. Then `f` is strictly decreasing on `[0, 1]` and `f(σ) > 0` for
`σ < σ̄1`. If moreover `p < 1`, `e(1, 1) > 0`, `e(1, 0) = 0`, and `e(1, ·)` and `π` are continuous, then
`σ̄1 < σ̄2 < 1`, `f(σ̄2) = 0`, `f(σ) > 0 ↔ σ < σ̄2` on `[0, 1]`, `σ̄2` strictly increases in `p`, and,
if `π` is differentiable in `e` at positive efforts, `σ̄2` strictly decreases in `g`.

**Formalization Note** The printed Claim needs three corrections. (i) `e(1, 1) > 0` and `p < 1`: for
`π(σ, e) = σ exp(-e)`, `g < 1` the effort is `0` throughout and `f(1) = 0`. (ii) `e(1, 0) = 0`, which
the appendix's "`e(1, σ, g) = 0`, for all `σ ≤ σ̄1(g)`" presumes at `σ = 0`: for
`π(σ, e) = ((1 + σ)/2) exp(-e)`, `g = 4`, `V = 2`, `c = 1`, `p = 11/20` one has
`e(1, σ) = log(2 + 2σ) > 0` and `f(0) = -1/16 < 0`, so `f < 0` on `[0, 1]`. (iii) (3) is strict and
`f(σ̄2) = 0`, so (3) holds iff `σ < σ̄2`, not `σ ≤ σ̄2`. The continuity of `e(1, ·)` is a reading of the
paper's differentiation of `e`; it is not automatic, and the first two conclusions do not need it.
`p̄(σ)`, the inverse of `σ̄2(p)`, is only a notation of the paper and is not stated. -/
theorem claim_threshold {V c g p : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hcV : c < V) (hg : 0 < g) (hp1 : p ≤ 1)
    (hπ : IsDetection π) (hE : IsEffort π g E) (hpV : c < p * V) :
    StrictAntiOn (gap π V c p E) (Icc 0 1) ∧
    (∀ σ ∈ Icc (0 : ℝ) 1, σ < sigmaBarOne E → 0 < gap π V c p E σ) ∧
    (p < 1 → 0 < E 1 1 → E 1 0 = 0 → ContinuousOn (E 1) (Icc 0 1) →
      ContinuousOn (Function.uncurry π) (Icc 0 1 ×ˢ Ici 0) →
      (sigmaBarOne E < sigmaBarTwo π V c p E ∧ sigmaBarTwo π V c p E < 1 ∧
        gap π V c p E (sigmaBarTwo π V c p E) = 0 ∧
        (∀ σ ∈ Icc (0 : ℝ) 1, 0 < gap π V c p E σ ↔ σ < sigmaBarTwo π V c p E)) ∧
      (∀ p' : ℝ, p < p' → p' ≤ 1 → sigmaBarTwo π V c p E < sigmaBarTwo π V c p' E) ∧
      (∀ (g' : ℝ) (E' : ℝ → ℝ → ℝ), g < g' → IsEffort π g' E' → E' 1 0 = 0 →
        ContinuousOn (E' 1) (Icc 0 1) →
        (∀ σ ∈ Icc (0 : ℝ) 1, ∀ e, 0 < e → DifferentiableAt ℝ (π σ) e) →
        sigmaBarTwo π V c p E' < sigmaBarTwo π V c p E)) := by sorry

end StrategicObfuscation
