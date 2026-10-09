-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_41_1_2_thm_I
-- name    : RamanujanNotebooks.entry_41_1_2_thm_I
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T15:57:00.408688+00:00
-- url     : https://prove2.me/theorems/a7f9a89a-0b28-4e73-a1dc-d4c60569fedc
-- title:
--   The exponential-series Master Theorem under Hardy conditions
-- statement:
--   Theorem I (Ramanujan's Master Theorem), p. 298, (1.1), under Hardy's conditions of p. 299: let `0 < δ < 1`, `A < π`, and let `φ(s)/Γ(s + 1)` be analytic on `Re s ≥ -δ` with `|φ(s)/Γ(s + 1)| ≤ C exp(P σ + A |t|)` there. Let `F` be Hardy's function attached to `ψ(s) = φ(s)/Γ(s + 1)` (the contour integral of p. 299, on a line `Re s = c`, `0 < c < δ`). Then `F(x) = ∑_{k ≥ 0} φ(k) (-x)^k / k!` for `0 < x < e^{-P}`, and for every real `n` with `0 < n < δ` the function `x^{n-1} F(x)` is integrable on `(0, ∞)` and `∫_0^∞ x^{n-1} F(x) dx = Γ(n) φ(-n)`. Differs from the printed source: Theorem I is printed with the sole hypothesis that `F` has the expansion `∑ φ(k)(-x)^k/k!` near `x = 0`, for unspecified `n`; the book says this is not rigorous and replaces it by Hardy's theorem, whose hypotheses, the definition of `F` on all of `(0, ∞)` by the contour integral, and the range `0 < n < δ` are used here (the correction is Hardy's, as reported by the book). H(δ,P,A) means complex differentiability on an open neighborhood of Re(s)≥-δ and a bound |ψ(σ+it)|≤K exp(Pσ+A|t|) for one real constant K throughout that half-plane. Ψ(ψ,c,x) denotes the real-parameter contour integral ∫_(t∈ℝ) [1/(2π)] [π/sin(π(c+it))] ψ(-c-it) x^(-c-it) dt, with the principal complex power and x>0. AUDIT_codex_b1 confirms Hardy’s correction; its ψ=1/Γ(s+1), n=.4 witness gives 2.2181595437576882230590540219076794508, with residual at working precision.
--
--   **Discrepancy from the printed source.** Differs from the printed source: Theorem I is printed with the sole hypothesis that `F` has the expansion `∑ φ(k)(-x)^k/k!` near `x = 0`, for unspecified `n`; the book says this is not rigorous and replaces it by Hardy's theorem, whose hypotheses, the definition of `F` on all of `(0, ∞)` by the contour integral, and the range `0 < n < δ` are used here (the correction is Hardy's, as reported by the book). AUDIT_codex_b1 confirms Hardy’s correction; its ψ=1/Γ(s+1), n=.4 witness gives 2.2181595437576882230590540219076794508, with residual at working precision.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 41, Theorem 1.2.thm.I, p. 298, eq. (1.1).

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch41_ch41HardyClass
import Definitions.Def_RamanujanNotebooks_ch41_ch41HardyPsi

namespace RamanujanNotebooks
theorem entry_41_1_2_thm_I (φ : ℂ → ℂ) (δ P A c : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hA : A < Real.pi) (hc0 : 0 < c) (hcδ : c < δ)
    (hφ : ch41HardyClass (fun s : ℂ => φ s / Complex.Gamma (s + 1)) δ P A) :
    (∀ x : ℝ, 0 < x → x < Real.exp (-P) →
        HasSum (fun k : ℕ => φ (k : ℂ) * (-(x : ℂ)) ^ k / (k.factorial : ℂ))
          (ch41HardyPsi (fun s : ℂ => φ s / Complex.Gamma (s + 1)) c x)) ∧
      ∀ n : ℝ, 0 < n → n < δ →
        MeasureTheory.IntegrableOn
            (fun x : ℝ => (x : ℂ) ^ ((n : ℂ) - 1) *
              ch41HardyPsi (fun s : ℂ => φ s / Complex.Gamma (s + 1)) c x) (Set.Ioi 0) ∧
          (∫ x in Set.Ioi (0 : ℝ), ((x : ℂ) ^ ((n : ℂ) - 1) *
              ch41HardyPsi (fun s : ℂ => φ s / Complex.Gamma (s + 1)) c x)) =
            Complex.Gamma (n : ℂ) * φ (-(n : ℂ)) := by sorry
end RamanujanNotebooks
