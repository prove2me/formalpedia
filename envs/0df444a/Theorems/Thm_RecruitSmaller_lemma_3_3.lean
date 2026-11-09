-- Prove2me | Theorems.Thm_RecruitSmaller_lemma_3_3
-- name    : RecruitSmaller.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:13:13.548752+00:00
-- url     : https://prove2.me/theorems/e782d614-6ce0-4ddd-83c6-878bd5394823
-- title:
--   Lemma 3.3 — rank-$i$ layer-cake identity (3.5)
-- statement:
--   Let $m\ge n\ge i\ge1$ and $k\ge n+1$, and let buyer values be i.i.d. with CDF $F_B$ and seller costs i.i.d. with CDF $F_S$. If $\mathrm{OPT}(m,n)<\infty$, then
--   $$
--   \mathbb E\Bigl[\bigl(b^{(i)}-s^{(i)}_k\bigr)\mathbb 1\bigl[b^{(i)}\ge s^{(i+1)}_k\bigr]-\bigl(b^{(i)}-s^{(i)}_n\bigr)^+\Bigr]=\int_{-\infty}^{\infty}\mathbb E_{b^{(i)}}\Bigl[\Delta_{n,k,i}\bigl(x,b^{(i)}\bigr)\mathbb 1\bigl[b^{(i)}\ge x\bigr]\Bigr]\,dx, \tag{3.5}
--   $$
--   where $\Delta_{n,k,i}(x,b^{(i)})=\Pr_{s_k}[s^{(i)}_k\le x\text{ and }s^{(i+1)}_k\le b^{(i)}]-\Pr_{s_n}[s^{(i)}_n\le x]$ (3.6).
--
--   More precisely, the statement asserts:
--   1. $\mathbb E_{b\sim F_B^m,s_k\sim F_S^k}[(b^{(i)}-s^{(i)}_k)\mathbb 1[b^{(i)}\ge s^{(i+1)}_k]]<\infty$;
--   2. $\mathbb E_{b\sim F_B^m,s_n\sim F_S^n}[(b^{(i)}-s^{(i)}_n)^+]<\infty$;
--   3. $x\mapsto\mathbb E_{b}[\Delta_{n,k,i}(x,b^{(i)})\mathbb 1[b^{(i)}\ge x]]$ is Lebesgue integrable on $\mathbb R$;
--   4. the difference of the two expectations equals the integral in (3.5).
--
--   This identity rewrites each rank's comparison between the recruited STR market and the original first-best as an integral over thresholds $x$.
--
--   **Formalization Note** Both expectations are Lebesgue integrals in $[0,\infty]$ of nonnegative integrands over the product laws; the left side of (3.5) is the difference of their real values.
--
--   Differences from the source:
--   - reading: E[X − Y] under a coupling of (b, s_n, s_k) with marginals F_Bᵐ, F_Sⁿ, F_Sᵏ → E[X] − E[Y], the two expectations taken over μBᵐ ⊗ μSᵏ and μBᵐ ⊗ μSⁿ and subtracted as reals; reason: the page's proof computes the two expectations separately and subtracts them; E[X − Y] = E[X] − E[Y] for any coupling once both are finite
--   - generalization: the identity (3.5) → (3.5) together with the finiteness of both expectations and the integrability of the x-integrand; reason: these are what the page's proof establishes to justify subtracting the two integrals; dropping them gives the page's identity
--   - encoding: distributions with CDFs F_B, F_S on ℝ → probability measures μB, μS on ℝ with F_B = cdf μB, F_S = cdf μS; reason: every CDF on ℝ is the CDF of exactly one probability measure; same instances
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.3, p.12, eqs. (3.5)–(3.6); proof p.24

import Mathlib
import Definitions.Def_RecruitSmaller_buyerOrd
import Definitions.Def_RecruitSmaller_sellerOrd
import Definitions.Def_RecruitSmaller_OPT
import Definitions.Def_RecruitSmaller_Delta

open MeasureTheory

namespace RecruitSmaller

/-- **Lemma 3.3** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.12, eqs. (3.5)–(3.6); proof p.24): let `m ≥ n ≥ i ≥ 1`
and `k ≥ n + 1`. If `OPT(m, n) < ∞`, then
`E[(b⁽ⁱ⁾ − s⁽ⁱ⁾ₖ) 𝟙[b⁽ⁱ⁾ ≥ s⁽ⁱ⁺¹⁾ₖ] − (b⁽ⁱ⁾ − s⁽ⁱ⁾ₙ)⁺] = ∫_{−∞}^{∞} E_{b⁽ⁱ⁾}[Δ_{n,k,i}(x, b⁽ⁱ⁾) 𝟙[b⁽ⁱ⁾ ≥ x]] dx`.

**Formalization Note** The two expectations are taken separately, over `μBᵐ ⊗ μSᵏ` and
`μBᵐ ⊗ μSⁿ`, in `ℝ≥0∞` (both integrands are nonnegative); the left side of (3.5) is their difference
of real values. The statement also asserts what the page's proof establishes to justify the
subtraction: both expectations are finite and the `x`-integrand is Lebesgue integrable. -/
theorem lemma_3_3 (m n k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (hnm : n ≤ m) (hk : n + 1 ≤ k)
    (μB μS : Measure ℝ) [IsProbabilityMeasure μB] [IsProbabilityMeasure μS]
    (hOPT : OPT m n μB μS ≠ ⊤) :
    let Ek : ENNReal := ∫⁻ ω : (Fin m → ℝ) × (Fin k → ℝ),
        ENNReal.ofReal ((buyerOrd ω.1 i - sellerOrd ω.2 i) *
          (if sellerOrd ω.2 (i + 1) ≤ buyerOrd ω.1 i then (1 : ℝ) else 0))
        ∂((Measure.pi fun _ : Fin m => μB).prod (Measure.pi fun _ : Fin k => μS))
    let En : ENNReal := ∫⁻ ω : (Fin m → ℝ) × (Fin n → ℝ),
        ENNReal.ofReal (max (buyerOrd ω.1 i - sellerOrd ω.2 i) 0)
        ∂((Measure.pi fun _ : Fin m => μB).prod (Measure.pi fun _ : Fin n => μS))
    let g : ℝ → ℝ := fun x => ∫ b : Fin m → ℝ,
        Delta μS n k i x (buyerOrd b i) * (if x ≤ buyerOrd b i then (1 : ℝ) else 0)
        ∂(Measure.pi fun _ : Fin m => μB)
    Ek ≠ ⊤ ∧ En ≠ ⊤ ∧ Integrable g ∧ Ek.toReal - En.toReal = ∫ x, g x := by sorry

end RecruitSmaller
