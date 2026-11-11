-- Prove2me | Theorems.Thm_QuadExt_Main_theorem_7_2
-- name    : QuadExt.Main.theorem_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:04:55.437478+00:00
-- url     : https://prove2.me/theorems/b8de5edf-564a-4854-8efb-3218c5d38177
-- title:
--   Theorem 7.2 — Algorithm 1 is a $(t, k, q, O(\delta))$-quadratic correlation breaker for pure quadratic sources, also under relaxed hypotheses (any LExt, CB)
-- statement:
--   For any $\delta \in (0,1)$ and positive integers $t, a, m$, Algorithm 1 yields a $(t, k, q, O(\delta))$-quadratic correlation breaker $\mathrm{QuadCB} : \mathbb F_2^n \times \mathbb F_2^d \times \mathbb F_2^a \to \mathbb F_2^m$ whenever
--   $$d \ge C t^5 \big(m + \log a \log(n/\delta)\big)^2, \qquad k \ge C t^2 d^4, \qquad q \le c \sqrt{k/(t d^2)},$$
--   for absolute constants $c, C > 0$. Moreover, the guarantee (Equation (5) of Definition 7.1) also holds when the entropy assumption of Item 1 and the uniformity assumption of Item 3 of Definition 7.1 are relaxed to $H^{\delta^4}_\infty(X) \ge k$ and $W \approx_{\delta^2} U_d$. Here Algorithm 1 uses a $(k', 2^{-4d_1}\delta^{32})$-strong linear seeded extractor $\mathrm{LExt}$ with seed length $d_0$ and output length $d_1$, where $k' = d_1 + 2\log(1/\varepsilon') = 9 d_1 + 64 \log(1/\delta)$ is the entropy requirement of Theorem 4.6 at error $\varepsilon' = 2^{-4d_1}\delta^{32}$, and a $(t, d/2, \delta/2)$-advice correlation breaker $\mathrm{CB}$, with $d_1 = O(t(m + t \log a \log(n/\delta)))$ and $d_0 = O(d_1 + \log(1/\delta))$.
--
--   The quadratic correlation breaker is applied $N$ times, with the outputs of a linear seeded extractor as seeds, inside the final extractor (Algorithm 2); correlation breaking is what makes the resulting bits a non-oblivious bit-fixing source.
--
--   Formally: for all $A_0, A_1 > 0$ (the constants of $d_1, d_0$) there are $c, C, C', c_0 > 0$ such that for all instances as above with $d_0 \le d$ and every such LExt and CB, Algorithm 1 is a $(t, k, q, C'\delta)$-quadratic correlation breaker with Definition 7.1's absolute constant $c_0$, and also satisfies the relaxed version with $\eta_X = \delta^4$, $\eta_W = \delta^2$.
--
--   Differences from the source:
--   - generalization: Algorithm 1 with LExt from Theorem 4.6 and CB from Theorem 4.13 → with every LExt and CB having the stated properties; reason: the paper's sub-routines are instances, so the statement specializes to the paper's.
--   - generalization: the fixed $O(\cdot)$ constants of $d_1, d_0$ → every $A_1, A_0 > 0$ with $d_1, d_0$ at most those bounds; reason: the paper's choice is one instance.
--   - reading: "the guarantee in Equation (4)" → Equation (5); reason: obvious typo, Equation (5) is the guarantee of Definition 7.1 whose Items 1 and 3 are being relaxed (INSIGHTS I5).
--   - reading: Algorithm 1's "$(k, 2^{-4d_1}\delta^{32})$ strong linear seeded [extractor] from Theorem 4.6" → a strong linear seeded extractor with Theorem 4.6's entropy requirement $d_1 + 2\log(1/\varepsilon') = 9d_1 + 64\log_2(1/\delta)$ at error $\varepsilon' = 2^{-4d_1}\delta^{32}$; reason: the proof of Theorem 7.2 applies Lemma 7.3 to subsources of derivative entropy $\Omega(d\sqrt t)$, far below the $k$ of Theorem 7.2, so LExt must extract at that lower entropy, which Theorem 4.6's extractor does; requiring LExt only at entropy $k$ would admit sub-routines the paper's proof does not cover.
--   - encoding: $d_0 \le d$ assumed; reason: $w_{[d_0]}$ must exist, so only cases where Algorithm 1 is undefined are excluded.
--   - encoding: $O(\delta)$ → $C'\delta$, used as the error parameter of Definition 7.1 (in Equation (5) and in $s \le k + c_0 \log(1/\delta')$); Definition 7.1's absolute constant → $c_0$ fixed with $c, C, C'$; reason: the source's "$(t, k, q, O(\delta))$" and "absolute constant" made explicit.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), pp. 20–21 (PDF 21–22), Theorem 7.2 and Algorithm 1

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Closeness
import Definitions.Def_QuadExt_Main_SeededExt
import Definitions.Def_QuadExt_Main_CorrBreakers

namespace QuadExt.Main

/-- **Theorem 7.2** (pp. 20–21), for Algorithm 1 run with any sub-routines of the stated
properties: for `δ ∈ (0, 1)` and positive integers `t, a, m`, `QuadCB` is a
`(t, k, q, O(δ))`-quadratic correlation breaker whenever `d ≥ Ct⁵(m + log a·log(n/δ))²`,
`k ≥ Ct²d⁴` and `q ≤ c√(k/(td²))`; moreover Equation (5) still holds when Items 1 and 3 of
Definition 7.1 are relaxed to `H^{δ⁴}_∞(X) ≥ k` and `W ≈_{δ²} U_d`. The sub-routine `LExt` is a
strong linear seeded extractor with Theorem 4.6's entropy requirement `d₁ + 2 log(1/ε)` at error
`ε = 2^{−4d₁}δ^{32}`, i.e. `9d₁ + 64 log₂(1/δ)`; `CB` is a `(t, d/2, δ/2)`-advice correlation breaker. -/
theorem theorem_7_2 :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
    ∃ c C C' c₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < C' ∧ 0 < c₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (t a m n d d0 d1 : ℕ), 1 ≤ t → 1 ≤ a → 1 ≤ m → ∀ h : d0 ≤ d,
    Alg1Params A₀ A₁ δ t a m n d0 d1 →
    ∀ k q : ℝ,
    C * (t : ℝ) ^ 5 * ((m : ℝ) + Real.logb 2 a * Real.logb 2 (n / δ)) ^ 2 ≤ (d : ℝ) →
    C * (t : ℝ) ^ 2 * (d : ℝ) ^ 4 ≤ k →
    q ≤ c * Real.sqrt (k / ((t : ℝ) * (d : ℝ) ^ 2)) →
    ∀ (LExt : (Fin n → ZMod 2) → (Fin d0 → ZMod 2) → (Fin d1 → ZMod 2))
      (CB : (Fin d → ZMod 2) → (Fin d1 → ZMod 2) → (Fin a → ZMod 2) → (Fin m → ZMod 2)),
    IsSLSE (9 * (d1 : ℝ) + 64 * Real.logb 2 (1 / δ))
      ((2 : ℝ) ^ (-(4 * d1 : ℝ)) * δ ^ 32) ((2 : ℝ) ^ (-(4 * d1 : ℝ)) * δ ^ 32) LExt →
    IsAdviceCB t ((d : ℝ) / 2) (δ / 2) CB →
    IsQuadCB c₀ t k q (C' * δ) (alg1 h LExt CB) ∧
      IsQuadCBRelaxed c₀ t k q (C' * δ) (δ ^ 4) (δ ^ 2) (alg1 h LExt CB) := by sorry

end QuadExt.Main
