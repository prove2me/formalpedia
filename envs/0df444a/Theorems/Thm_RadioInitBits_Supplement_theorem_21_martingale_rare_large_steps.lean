-- Prove2me | Theorems.Thm_RadioInitBits_Supplement_theorem_21_martingale_rare_large_steps
-- name    : RadioInitBits.Supplement.theorem_21_martingale_rare_large_steps
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:06:41.842549+00:00
-- url     : https://prove2.me/theorems/91a6ce32-70d2-46bd-b423-fc1132fe9a21
-- title:
--   Theorem 21 — martingale concentration with rare large steps: $\Pr(|M_N-M_0|>Cb\sqrt N)<2e^{-C^2/2}+N\alpha\ell/b$
-- statement:
--   This is a concentration inequality for martingales whose steps are bounded by $b$ "most of the time", with rare large steps of bounded conditional mean size.
--
--   Let $(\Omega,\mathcal F,\Pr)$ be a probability space with a filtration $(\mathcal F_j)_{j\ge0}$, and let $M=(M_j)_{j\ge0}$ be a real-valued martingale with respect to it. Write $D_j=M_j-M_{j-1}$ for $j\ge1$. Let $b>0$, $0<\alpha<1$ and $\ell\ge b$, and suppose that for every $j\ge1$,
--
--   1. $\Pr\big(|D_j|>b\big)<\alpha$;
--   2. almost surely, $\mathbb E\big[|D_j|\,\mathbf 1\{|D_j|>b\}\mid\mathcal F_{j-1}\big]\le \ell\cdot\Pr\big(|D_j|>b\mid\mathcal F_{j-1}\big)$, i.e. a large step has conditional mean size at most $\ell$.
--
--   Then for every positive integer $N$ and every $C>0$,
--   $$\Pr\big(|M_N-M_0|>Cb\sqrt N\big)\ <\ 2\exp\!\Big(-\frac{C^2}{2}\Big)+\frac{N\alpha\ell}{b}.$$
--
--   It extends the Azuma–Hoeffding inequality, which needs almost surely bounded steps; the paper uses it to control the drift of a potential function in its energy lower bound.
--
--   **Formalization Note** Hypothesis (1) is stated as printed (unconditionally); the hypothesis on the mean size of a large step holds for every history ("always exists", "uniformly bounded"). Conditional probabilities are conditional expectations of indicators (`μ[·|ℱ (j-1)]`). The bound on the conditional mean of a large step is written multiplicatively, so no division by a possibly vanishing conditional probability occurs.
--
--   Differences from the source:
--   - reading: E[|Mj − Mj−1| | |Mj − Mj−1| > b] always exists and is uniformly bounded above by ℓ → for every j ≥ 1, almost surely E[|D_j|·1{|D_j| > b} | ℱ_{j−1}] ≤ ℓ·Pr(|D_j| > b | ℱ_{j−1}); reason: 'always exists' and 'uniformly bounded' refer to every history, and the proof uses the bound step by step conditionally on the past ('the disk of radius b around M_{j−1}', the martingale identity (2)); hypothesis (1) is kept unconditional as printed
--   - generalization: the conditional mean of a large step exists (the conditioning event has positive probability) and is at most ℓ → the multiplicative form E[|D|·1{|D| > b} | ℱ] ≤ ℓ·Pr(|D| > b | ℱ), which also holds where the conditional probability vanishes; reason: on the source's domain (positive conditional probability) the two forms are equivalent, so it specializes to the source's claim
--   - generalization: a martingale M with |·|, j ranging over steps → a real-valued martingale for an arbitrary filtration ℱ on a probability space, steps j ≥ 1 with D_j = M j − M (j − 1); reason: |·| makes M real-valued; taking ℱ the natural filtration of M gives the source's statement; step 0 has no predecessor
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version §3.7, Theorem 21, p.14 (PDF p.35), proof pp.14–15 (PDF pp.35–36); short version p.8 (PDF p.10)

import Mathlib

set_option autoImplicit false

namespace RadioInitBits

namespace Supplement

open MeasureTheory

/-- **Theorem 21** (martingale concentration with rare large steps). Let `b > 0`, `0 < α < 1` and
`ℓ ≥ b`. Let `M` be a real martingale with respect to a filtration `ℱ` on a probability space,
with steps `D_j = M_j − M_{j−1}` (`j ≥ 1`) such that

1. `Pr(|D_j| > b) < α` (hypothesis (1)), and
2. conditionally on the past `ℱ_{j−1}`,
   `E[|D_j| · 1{|D_j| > b} | ℱ_{j−1}] ≤ ℓ · Pr(|D_j| > b | ℱ_{j−1})` almost surely, i.e. the
   conditional mean size of a large step is at most `ℓ` whatever the history.

Then for every positive integer `N` and every `C > 0`,
`Pr(|M_N − M_0| > C b √N) < 2 exp(−C²/2) + N α ℓ / b`.

D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version §3.7, Theorem 21, p.14 (PDF p.35):
"Let b > 0 and 0 < α < 1. Let M be a martingale such that for all j Pr(|Mj − Mj−1| > b) < α. (1)
Moreover, suppose E[|Mj − Mj−1| | |Mj − Mj−1| > b] always exists and is uniformly bounded above by
ℓ, where ℓ ≥ b. Then, for all positive integers N and all C > 0,
Pr(|MN − M0| > Cb√N) < 2 exp(−C²/2) + Nαℓ/b"; also short version p.8 (PDF p.10).

**Formalization Note** Hypothesis (1) is stated as printed, unconditionally. The second hypothesis
is read conditionally on the past `ℱ (j − 1)`: the conditional mean of a large step must "always
exist" and be "uniformly bounded", and the proof works step by step "around M_{j−1}" (its union
bound needs only the unconditional (1), since the per-step failure probability
`αⱼℓ/(b − αⱼb + αⱼℓ)` is concave in the conditional `αⱼ`). The bound `E[|D| | |D| > b] ≤ ℓ` is written multiplicatively, which avoids dividing by a
conditional probability that may vanish (where the paper's conditional mean is undefined, the
multiplicative form holds trivially). `M` is adapted to an arbitrary filtration. -/
theorem theorem_21_martingale_rare_large_steps
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ μ)
    {b α ℓ : ℝ} (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1) (hℓ : b ≤ ℓ)
    (h1 : ∀ j : ℕ, 1 ≤ j → μ {ω | b < |M j ω - M (j - 1) ω|} < ENNReal.ofReal α)
    (h2 : ∀ j : ℕ, 1 ≤ j → ∀ᵐ ω ∂μ,
      μ[fun ω' => |M j ω' - M (j - 1) ω'| *
          {ω'' | b < |M j ω'' - M (j - 1) ω''|}.indicator (fun _ => (1 : ℝ)) ω' | ℱ (j - 1)] ω ≤
        ℓ * μ[{ω' | b < |M j ω' - M (j - 1) ω'|}.indicator (fun _ => (1 : ℝ)) | ℱ (j - 1)] ω)
    (N : ℕ) (hN : 1 ≤ N) (C : ℝ) (hC : 0 < C) :
    μ {ω | C * b * Real.sqrt N < |M N ω - M 0 ω|} <
      ENNReal.ofReal (2 * Real.exp (-C ^ 2 / 2) + N * α * ℓ / b) := by sorry

end Supplement

end RadioInitBits
