-- Prove2me | Theorems.Thm_QuadExt_Main_lemma_7_3
-- name    : QuadExt.Main.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:05:08.455813+00:00
-- url     : https://prove2.me/theorems/45eee661-87e2-497a-9aa4-1e263446648f
-- title:
--   Lemma 7.3 — Algorithm 1 breaks correlations for a high-derivative-entropy source whose seeds are functions of $Z$ (any LExt, CB)
-- statement:
--   Consider Algorithm 1 (QuadCB) with error parameter $\delta \in (0,1)$, positive integers $t, a, m$, parameters $d_1 = O(t(m + t\log a \log(n/\delta)))$, $d_0 = O(d_1 + \log(1/\delta))$, $d = O(t^5(m + \log a \log(n/\delta))^2)$, and sub-routines $\mathrm{LExt}$, a $(k, 2^{-4d_1}\delta^{32})$-strong linear seeded extractor with seed length $d_0$ and output length $d_1$, and $\mathrm{CB}$, a $(t, d/2, \delta/2)$-advice correlation breaker with seed length $d_1$. Let $X = f(Y, Z)$ with $f$ quadratic, $Y = U_s$, $Z$ independent of $Y$, $f(Y, Z) = f_1(Y) + f_2(Y, Z) + f_3(Z)$, $f_2$ bilinear and $H_\infty(\partial_a f_1(Y)) \ge k$ for all $a \ne 0$. Let $W, W^1, \dots, W^t$ be functions of $Z$ with $W = U_d$, and let $\alpha \ne \alpha_i$ for all $i$. There is a large constant $C$ such that if $s, k \ge C(d_1 + \log(1/\delta))$, then
--   $$\big(\mathrm{QuadCB}(X, W, \alpha) \approx_{O(\delta)} U_m\big) \mid \{\mathrm{QuadCB}(X, W^i, \alpha^i)\}_{i \in [t]}.$$
--   Lemma 7.3 is the core of Theorem 7.2: after the structure theorem has produced sources of this form, it gives the correlation-breaking guarantee.
--
--   Formally: for all $A_0, A_1 > 0$ there are $A_d, C, C' > 0$ such that whenever $d_1 \le A_1 t(m + t \log_2 a \log_2(n/\delta))$, $d_0 \le A_0(d_1 + \log_2(1/\delta))$, $d \ge A_d t^5 (m + \log_2 a \log_2(n/\delta))^2$ and $d_0 \le d$, the conclusion holds with error $C'\delta$, for every such LExt and CB.
--
--   Differences from the source:
--   - generalization: Algorithm 1 with LExt from Theorem 4.6 and CB from Theorem 4.13 → with every LExt and CB having the properties Algorithm 1 asks of them; reason: the paper's sub-routines are instances, so the statement specializes to the paper's.
--   - generalization: the fixed $O(\cdot)$ constants of $d_1$ and $d_0$ in Algorithm 1 → every $A_1, A_0 > 0$, with $d_1, d_0$ at most those bounds (the remaining constants chosen after $A_0, A_1$); reason: the paper's choice is one instance, so this specializes to the paper's.
--   - reading: Algorithm 1's "$d = O(t^5(m + \log a \log(n/\delta))^2)$" → $d \ge A_d t^5(m + \log_2 a \log_2(n/\delta))^2$; reason: $d$ is chosen of this order and the proof needs $d$ large (Theorem 7.2 states the same lower bound).
--   - reading: $\delta \in (0,1)$ and $t, a, m$ positive integers; reason: the ranges of Algorithm 1's parameters in Theorem 7.2.
--   - encoding: $d_0 \le d$ assumed; reason: $w_{[d_0]}$ must exist, so this only excludes cases where Algorithm 1 is undefined.
--   - encoding: $Z$ → any distribution on $\mathbb F_2^z$; $W, W^i$ → any functions $p, p_i$ of $Z$; "a large constant $C$" and $O(\delta)$ → constants $C, C'$ fixed before all instance parameters; reason: the source's quantifiers made explicit.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 21 (PDF 22), Lemma 7.3 and Algorithm 1

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Closeness
import Definitions.Def_QuadExt_Main_SeededExt
import Definitions.Def_QuadExt_Main_CorrBreakers

namespace QuadExt.Main

/-- **Lemma 7.3** (p. 21), for Algorithm 1 run with any sub-routines `LExt` (a
`(k, 2^{−4d₁}δ^{32})`-strong linear seeded extractor) and `CB` (a `(t, d/2, δ/2)`-advice correlation
breaker) of the algorithm's parameters: if `X = f(Y, Z) = f₁(Y) + f₂(Y, Z) + f₃(Z)` with `f`
quadratic, `Y = U_s` independent of `Z`, `f₂` bilinear, `H_∞(∂_a f₁(Y)) ≥ k` for all `a ≠ 0`,
`W = p(Z)` uniform and `W^i = p_i(Z)`, `α ≠ α_i`, and `s, k ≥ C(d₁ + log(1/δ))`, then
`(QuadCB(X, W, α) ≈_{O(δ)} U_m) | {QuadCB(X, W^i, α^i)}_{i∈[t]}`. -/
theorem lemma_7_3 :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
    ∃ Ad C C' : ℝ, 0 < Ad ∧ 0 < C ∧ 0 < C' ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (t a m n d d0 d1 : ℕ), 1 ≤ t → 1 ≤ a → 1 ≤ m → ∀ h : d0 ≤ d,
    Alg1Params A₀ A₁ δ t a m n d0 d1 →
    Ad * (t : ℝ) ^ 5 * ((m : ℝ) + Real.logb 2 a * Real.logb 2 (n / δ)) ^ 2 ≤ (d : ℝ) →
    ∀ (k : ℝ) (LExt : (Fin n → ZMod 2) → (Fin d0 → ZMod 2) → (Fin d1 → ZMod 2))
      (CB : (Fin d → ZMod 2) → (Fin d1 → ZMod 2) → (Fin a → ZMod 2) → (Fin m → ZMod 2)),
    IsSLSE k ((2 : ℝ) ^ (-(4 * d1 : ℝ)) * δ ^ 32) ((2 : ℝ) ^ (-(4 * d1 : ℝ)) * δ ^ 32) LExt →
    IsAdviceCB t ((d : ℝ) / 2) (δ / 2) CB →
    ∀ (s z : ℕ) (f : (Fin s ⊕ Fin z → ZMod 2) → (Fin n → ZMod 2))
      (f₁ : (Fin s → ZMod 2) → (Fin n → ZMod 2))
      (f₂ : (Fin s → ZMod 2) → (Fin z → ZMod 2) → (Fin n → ZMod 2))
      (f₃ : (Fin z → ZMod 2) → (Fin n → ZMod 2))
      (μZ : PMF (Fin z → ZMod 2)) (p : (Fin z → ZMod 2) → (Fin d → ZMod 2))
      (ps : Fin t → (Fin z → ZMod 2) → (Fin d → ZMod 2))
      (α : Fin a → ZMod 2) (αs : Fin t → Fin a → ZMod 2),
    IsQuadraticMap f → (∀ y w, f (join y w) = f₁ y + f₂ y w + f₃ w) → IsBilinear f₂ →
    (∀ b : Fin s → ZMod 2, b ≠ 0 → k ≤ SSNonExt.minEntropy (source (dirDeriv b f₁))) →
    μZ.map p = PMF.uniformOfFintype (Fin d → ZMod 2) →
    (∀ i, α ≠ αs i) →
    C * ((d1 : ℝ) + Real.logb 2 (1 / δ)) ≤ (s : ℝ) →
    C * ((d1 : ℝ) + Real.logb 2 (1 / δ)) ≤ k →
    CondCloseUnif (C' * δ) ((indepPair (unif (Fin s)) μZ).map fun yz =>
      (alg1 h LExt CB (f (join yz.1 yz.2)) (p yz.2) α,
        fun i => alg1 h LExt CB (f (join yz.1 yz.2)) (ps i yz.2) (αs i))) := by sorry

end QuadExt.Main
