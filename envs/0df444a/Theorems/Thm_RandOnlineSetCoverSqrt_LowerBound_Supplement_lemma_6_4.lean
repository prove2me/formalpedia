-- Prove2me | Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_Supplement_lemma_6_4
-- name    : RandOnlineSetCoverSqrt.LowerBound.Supplement.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:14:06.887298+00:00
-- url     : https://prove2.me/theorems/27d6aca3-2e56-4d6b-a738-8dc0ad62359f
-- title:
--   Lemma 6.4 — entropy estimate for $R_m(\alpha)$
-- statement:
--   There exists a constant $C>0$ such that for every integer $m\ge2$ and every real $\alpha\ge1$,
--   $$m^{-C}\bigl(1+e^{-\alpha H(1/\alpha)}\bigr)^m\ \le\ R_m(\alpha)\ \le\ m^{C}\bigl(1+e^{-\alpha H(1/\alpha)}\bigr)^m,$$
--   where $R_m(\alpha)=\max_{0\le k\le\lfloor m/\alpha\rfloor}\binom mk/\binom{\lfloor\alpha k\rfloor}{k}$ (the $k=0$ term being $1$) and $H(x)=-x\log x-(1-x)\log(1-x)$ is the binary entropy in nats, $H(1)=0$. At $\alpha=1$ the base is $2$.
--
--   The lower estimate turns the communication bound of Lemma 6.2 into the $\Omega(m/\log m)$ bound of Theorem 1.5.
--
--   Differences from the source:
--   - encoding: H(x) = −x log x − (1−x) log(1−x) with H(0)=H(1)=0, natural log → Mathlib Real.binEntropy; reason: the same function, including the boundary values
--   - encoding: m^{−C}, m^{C} and the maximum defining R_m(α) → real powers of (m:ℝ) and a real sup over k ∈ {0,…,⌊m/α⌋} with natural-number floors; reason: m ≥ 2 makes the real power standard; floors of nonnegative reals agree with the integer floor
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Lemma 6.4, printed p. 18 / PDF p. 19; proof Appendix A, printed pp. 24–25 / PDF pp. 25–26

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_BinomialRatio

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement

/-- Lemma 6.4, printed p. 18 / PDF p. 19 (proof Appendix A, PDF pp. 25-26). One constant `C`
for every natural `m ≥ 2` and every real `α ≥ 1`; `H = Real.binEntropy` (natural logarithm,
`H 0 = H 1 = 0`). -/
theorem lemma_6_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ α : ℝ, 1 ≤ α →
      (m : ℝ) ^ (-C) * (1 + Real.exp (-(α * Real.binEntropy (1 / α)))) ^ m ≤ Rm m α ∧
      Rm m α ≤ (m : ℝ) ^ C * (1 + Real.exp (-(α * Real.binEntropy (1 / α)))) ^ m := by sorry

end RandOnlineSetCoverSqrt.LowerBound.Supplement
