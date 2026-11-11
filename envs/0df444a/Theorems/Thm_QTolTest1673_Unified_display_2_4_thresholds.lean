-- Prove2me | Theorems.Thm_QTolTest1673_Unified_display_2_4_thresholds
-- name    : QTolTest1673.Unified.display_2_4_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:48.129807+00:00
-- url     : https://prove2.me/theorems/df48b53e-c0fa-47d0-b218-e9b0305164de
-- title:
--   §2.4 displays and equation (1) (p. 16) — YES/NO Fourier-mass thresholds and $\Gamma=2(\varepsilon_2-2\varepsilon_1(1-\varepsilon_1))$
-- statement:
--   Let $0\le\varepsilon_1<\varepsilon_2<1/2$, $\alpha=1-2\varepsilon_1$, $\beta=1-2\varepsilon_2$, and let $f:\mathbb F_2^n\to\{\pm1\}$. For Fourier dimensionality testing ($\mathcal C=L_{n,k}$, $\mathcal V=\mathcal V_k^{\dim}$) and for junta testing ($\mathcal C=J_{n,k}$, $\mathcal V=\mathcal V_k^{\mathrm{junta}}$):
--
--   1. (YES) if $\operatorname{dist}(f,\mathcal C)\le\varepsilon_1$, then some $V\in\mathcal V$ has $W_V\ge\alpha^2$;
--   2. (NO) if $\operatorname{dist}(f,\mathcal C)\ge\varepsilon_2$, then every $V\in\mathcal V$ has $W_V\le\beta$.
--
--   Moreover, equation (1):
--   $$\Gamma=\alpha^2-\beta=(1-2\varepsilon_1)^2-(1-2\varepsilon_2)=2\bigl(\varepsilon_2-2\varepsilon_1(1-\varepsilon_1)\bigr).$$
--
--   Here $W_V=\sum_{u\in V}\hat f(u)^2$. When $\Gamma>0$ the two promises are separated in Fourier mass, so uniform estimation of all candidate masses to accuracy below $\Gamma/2$ decides the tolerant problem.
--
--   Differences from the source:
--   - encoding: $f:\mathbb F_2^n\to\{\pm1\}$ → its bit function `BoolFn n` with $f=(-1)^{b_f}$ (`toSign`); reason: a bijection; the XOR oracle adds $b_f=(1-f)/2$; same instances
--   - encoding: YES: some $V\in\mathcal V$ has $W_V\ge\alpha^2$; NO: every $V\in\mathcal V$ has $W_V\le\beta$, for YES/NO inputs → implications from $\operatorname{dist}(f,\mathcal C)\le\varepsilon_1$, resp. $\ge\varepsilon_2$, stated for both pairs $(L_{n,k},\mathcal V_k^{\dim})$ and $(J_{n,k},\mathcal V_k^{\mathrm{junta}})$; reason: the source states the displays for a generic candidate family $\mathcal V$ of either problem; both instances are stated
--   - encoding: coordinates $[n]=\{1,\dots,n\}$ → `Fin n` = $\{0,\dots,n-1\}$; reason: index base only; same instances
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), source.pdf SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, §2.4 displays and equation (1), p. 16

import Definitions.Def_QTolTest1673_Unified_Classes

namespace QTolTest1673.Unified

open FourierDimTesting102.Quantum

/-- §2.4 displays and equation (1), p. 16. Let `0 ≤ ε₁ < ε₂ < 1/2`, `α = 1 − 2ε₁`,
`β = 1 − 2ε₂`. For both properties (`L_{n,k}` with `V_k^dim`, `J_{n,k}` with `V_k^junta`):
a YES input (`dist(f, C) ≤ ε₁`) has some candidate `V` with `W_V ≥ α²`, and a NO input
(`dist(f, C) ≥ ε₂`) has `W_V ≤ β` for every candidate. Moreover
`Γ = α² − β = 2(ε₂ − 2ε₁(1 − ε₁))`. -/
theorem display_2_4_thresholds (n k : ℕ) (f : BoolFn n) (ε₁ ε₂ : ℝ) (hε₁ : 0 ≤ ε₁)
    (hε₁₂ : ε₁ < ε₂) (hε₂ : ε₂ < 1 / 2) :
    (distToSet f (linJunta n k) ≤ ε₁ → ∃ W ∈ famDim n k, (1 - 2 * ε₁) ^ 2 ≤ wtIn f W) ∧
      (ε₂ ≤ distToSet f (linJunta n k) → ∀ W ∈ famDim n k, wtIn f W ≤ 1 - 2 * ε₂) ∧
      (distToSet f (junta n k) ≤ ε₁ → ∃ W ∈ famJunta n k, (1 - 2 * ε₁) ^ 2 ≤ wtIn f W) ∧
      (ε₂ ≤ distToSet f (junta n k) → ∀ W ∈ famJunta n k, wtIn f W ≤ 1 - 2 * ε₂) ∧
      (1 - 2 * ε₁) ^ 2 - (1 - 2 * ε₂) = 2 * (ε₂ - 2 * ε₁ * (1 - ε₁)) := by sorry

end QTolTest1673.Unified
