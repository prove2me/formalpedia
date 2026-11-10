-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_B_6
-- name    : PrivGaussMS.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:54.150366+00:00
-- url     : https://prove2.me/theorems/c6c31dc2-eeb2-4c97-aea2-fa409fe1f034
-- title:
--   Lemma B.6 — privacy of $\mathcal A$: $(\varepsilon,\delta/4)$-DP under (21)
-- statement:
--   There is a constant $C_0>0$ such that every $C_{\mathrm{priv}}\ge C_0$ has the following property. Let $d,m\ge1$, $0<\varepsilon\le1$, $0<\delta<1$ and integers $\lambda,a_0\ge1$, and take
--   $$\ell=1+\frac2\varepsilon\log\frac{32}\delta,\qquad t=\log\frac{C_{\mathrm{priv}}(d+1)}\delta,\qquad k=a_0+\lceil2\ell\rceil+1.$$
--   If
--   $$n\ge C_{\mathrm{priv}}\Bigl[k\lambda+m+d+t+\frac{\lambda(\sqrt{mt}+t)}{\varepsilon}\Bigr],\tag{21}$$
--   then the sampler $\mathcal A$ (Algorithm 4) on $n$ records of $\mathbb R^d$ is $(\varepsilon,\delta/4)$-differentially private over all datasets.
--
--   This is the privacy of the private branch of the mechanism.
--
--   Differences from the source:
--   - reading: 'for a sufficiently large universal constant C_priv' → ∃ C₀ > 0, ∀ C_priv ≥ C₀, before d, m, n; t depends on C_priv; reason: the stronger of the two readings; the proof only enlarges C_priv
--   - reading: the lemma's unstated ranges → d, m ≥ 1, 0 < ε ≤ 1, 0 < δ < 1, integers λ, a0 ≥ 1; reason: standing assumptions of §3 (p.8) and §B.3.3 (p.39)
--   - encoding: WeightedResample requires C ≻ 0 and b > m → if the test accepts with B ⊁ 0 or b ≤ m, A returns ⊥; reason: the paper shows acceptance forces B ≻ 0 and b > m under the parameters (p.40); no instance changes
--   - encoding: a randomized mechanism and its output law → a family of output laws, with IsDPM asserting that each is a probability measure and applying the published IsDP; reason: Lean pushes a non-measurable map to the zero measure, under which DP would hold vacuously; the assertion rules this out and changes no instance
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma B.6, p.42, eq. (21); Algorithm 4, p.40

import Mathlib
import Definitions.Def_PrivGaussMS_Sampler

open MeasureTheory ProbabilityTheory

namespace PrivGaussMS

/-- **Lemma B.6** (Privacy of `A`), Moayedi, Yassaee, Ebrahimi, *Optimal Private Gaussian
Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…), p.42, eq. (21).

For a sufficiently large universal constant `C_priv`, take `ℓ = 1 + (2/ε) log(32/δ)`,
`t = log(C_priv(d + 1)/δ)`, `k = a0 + ⌈2ℓ⌉ + 1`. If
`n ≥ C_priv[kλ + m + d + t + λ(√(mt) + t)/ε]` (21), then `A` (Algorithm 4) is `(ε, δ/4)`-DP.

**Formalization Note.** "For a sufficiently large universal constant `C_priv`" is read as: there
is `C₀ > 0` such that every `C_priv ≥ C₀` works; `C_priv` precedes `d, m, n`, and `t` depends on it.
The standing ranges are those of §3 (`0 < ε ≤ 1`, `0 < δ < 1`, `d, m ≥ 1`, p.8) and §B.3.3 (integers
`λ, a0 ≥ 1`, p.39). Privacy is over all datasets of `(ℝ^d)^n`. `A` returns `⊥` if its test accepts
with `B ⊁ 0` or `b ≤ m` (see `samplerAOut`). -/
theorem lemma_B_6 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Cpriv : ℝ, C₀ ≤ Cpriv →
      ∀ n m d : ℕ, 1 ≤ m → 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
      ∀ lam a0 : ℕ, 1 ≤ lam → 1 ≤ a0 →
        let ℓ : ℝ := 1 + (2 / ε) * Real.log (32 / δ)
        let t : ℝ := Real.log (Cpriv * ((d : ℝ) + 1) / δ)
        let k : ℕ := a0 + ⌈2 * ℓ⌉₊ + 1
        Cpriv * ((k : ℝ) * lam + m + d + t + lam * (Real.sqrt ((m : ℝ) * t) + t) / ε) ≤ n →
        IsDPM (samplerA n m d lam k a0 ℓ ε) ε (δ / 4) := by sorry

end PrivGaussMS
