-- Prove2me | Theorems.Thm_WassChanceCvx_lemma_7_genMean_monotone_continuous
-- name    : WassChanceCvx.lemma_7_genMean_monotone_continuous
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:17.260158+00:00
-- url     : https://prove2.me/theorems/5ad3bc67-3001-4da4-ba4c-6b123c4c443d
-- title:
--   Lemma 7 (corrected: continuity at $\pm\infty$ only for $\theta\in(0,1)$) — $\alpha\mapsto m_\alpha(a,b;\theta)$ is nondecreasing and continuous
-- statement:
--   Let $a,b\ge0$. Then:
--
--   1. for every $\theta\in[0,1]$, $\alpha\mapsto m_\alpha(a,b;\theta)$ is nondecreasing on $[-\infty,+\infty]$;
--   2. for every $\theta\in(0,1)$, $\alpha\mapsto m_\alpha(a,b;\theta)$ is continuous on $[-\infty,+\infty]$;
--   3. for every $\theta\in[0,1]$, $\alpha\mapsto m_\alpha(a,b;\theta)$ is continuous on $\mathbb R$.
--
--   Monotonicity means that an α-concave function or measure is β-concave for every $\beta\le\alpha$, which Theorem 1's proof uses to lower the exponent.
--
--   **Formalization Note** $[-\infty,+\infty]$ is `EReal` with its order topology.
--
--   Differences from the source:
--   - correction: $\alpha\mapsto m_\alpha(a,b;\theta)$ continuous on $[-\infty,+\infty]$ for all $\theta$ → continuous on $[-\infty,+\infty]$ for $\theta\in(0,1)$ and on $\mathbb R$ for $\theta\in[0,1]$; nondecreasing for all $\theta\in[0,1]$; reason: the printed claim is false: $a=1$, $b=2$, $\theta=1$ gives $m_\alpha=1$ for every real $\alpha$ but $m_{+\infty}=\max\{1,2\}=2$
--   - encoding: $a,b\in\mathbb R_+$, $\theta\in[0,1]$ implicit in $m_\alpha$ → hypotheses $0\le a$, $0\le b$ and the stated ranges of $\theta$; reason: the domain of Definition 1's $m_\alpha$
--   - encoding: $\alpha\in\overline{\mathbb R}$ → `α : EReal`; reason: same values $[-\infty,+\infty]$
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Lemma 7, p.31

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_genMean

namespace WassChanceCvx

/-- **Lemma 7 (monotonicity and continuity of `α ↦ m_α`), corrected.**
Shen, Jiang, arXiv:2111.02486v2, Lemma 7 (Lemma 4.8 in [SDR09]), p.31: "The mapping
`α ↦ m_α(a, b; θ)` is nondecreasing and continuous."

For `a, b ≥ 0`: (1) `α ↦ m_α(a, b; θ)` is nondecreasing on `[−∞, +∞]` for every `θ ∈ [0, 1]`;
(2) it is continuous on `[−∞, +∞]` for every `θ ∈ (0, 1)`; (3) it is continuous on `ℝ` for every
`θ ∈ [0, 1]`.

**Correction.** Continuity on `[−∞, +∞]` fails at `θ ∈ {0, 1}`: for `a = 1`, `b = 2`, `θ = 1`,
`m_α = 1` for every real `α` but `m_{+∞} = max{1, 2} = 2`. The statement keeps monotonicity for
all `θ` and continuity at `±∞` for `θ ∈ (0, 1)`, and continuity on the reals for all `θ`.

**Formalization Note.** `[−∞, +∞]` is `EReal` with its order topology. `m_α(a, b; θ)` is the
published `KallMayerSLP.GenConcave.genMean α θ a b`. -/
theorem lemma_7_genMean_monotone_continuous (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → Monotone (fun α : EReal => KallMayerSLP.GenConcave.genMean α θ a b)) ∧
      (∀ θ : ℝ, 0 < θ → θ < 1 → Continuous (fun α : EReal => KallMayerSLP.GenConcave.genMean α θ a b)) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → Continuous (fun α : ℝ => KallMayerSLP.GenConcave.genMean (α : EReal) θ a b)) := by sorry

end WassChanceCvx
