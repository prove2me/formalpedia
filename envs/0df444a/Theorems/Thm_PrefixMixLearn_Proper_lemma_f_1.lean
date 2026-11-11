-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_lemma_f_1
-- name    : PrefixMixLearn.Proper.lemma_f_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:46:42.631455+00:00
-- url     : https://prove2.me/theorems/dbe8720e-c7d1-49a0-b024-c0dd5684384b
-- title:
--   Lemma F.1 — global mean–direction restoration: TV cost E_mean/√(2u) + q(2r + D_dir)D_dir/(2√2 u)
-- statement:
--   Let $0<\alpha<1/2$, $u=\alpha(1-\alpha)$, $M=(1-w)Q_\nu+wQ_\mu$ with $0<w<1$ and $\mu,\nu\in[\alpha,1-\alpha]^T$; $q=w(1-w)$, $d=\mu-\nu$, $r=\|d\|_2$, $m=(1-w)\nu+w\mu$. For arbitrary raw vectors $\tilde\nu,\tilde\mu\in\mathbb R^T$ put $\tilde d=\tilde\mu-\tilde\nu$, $\tilde m=(1-w)\tilde\nu+w\tilde\mu$, $E_{\mathrm{mean}}=\|\tilde m-m\|_2$, $D_{\mathrm{dir}}=\|\tilde d-d\|_2$. Clip $\tilde m$ to $\hat m$ and project $\tilde d$ onto $I(\hat m,w)$ to obtain $\hat d$. The resulting proper balanced mixture $\hat M=M(\hat m,\hat d,w)$ satisfies
--   $$d_{TV}(M,\hat M)\le\frac{E_{\mathrm{mean}}}{\sqrt{2u}}+\frac{q}{2\sqrt2\,u}(2r+D_{\mathrm{dir}})D_{\mathrm{dir}}.$$
--   This converts the coupled raw-profile errors of the unmixing into a law error.
--
--   Differences from the source:
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 39 (PDF 41), Lemma F.1, (F.1)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Geometry

namespace PrefixMixLearn.Proper

/-- Lemma F.1 (global mean–direction restoration): for `M = (1 − w)Q_ν + wQ_μ` with `0 < w < 1`
and balanced `μ, ν`, and arbitrary raw vectors `ν̃, μ̃`, clipping `m̃ = (1 − w)ν̃ + wμ̃` to `m̂` and
projecting `d̃ = μ̃ − ν̃` onto `I(m̂, w)` gives a proper balanced mixture `M̂ = M(m̂, d̂, w)` with
`d_TV(M, M̂) ≤ E_mean/√(2u) + (q/(2√2 u))(2r + D_dir) D_dir` (F.1). -/
theorem lemma_f_1 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 / 2) (T : ℕ) (w : ℝ) (hw0 : 0 < w)
    (hw1 : w < 1) (ν μ : Fin T → ℝ) (hν : InBox α ν) (hμ : InBox α μ) (νt μt : Fin T → ℝ) :
    restore α w νt μt ∈ M2Class α T ∧
      tv (mixLaw w ν μ) (restore α w νt μt) ≤
        l2 (fun i => ((1 - w) * νt i + w * μt i) - ((1 - w) * ν i + w * μ i)) /
            Real.sqrt (2 * uOf α) +
          w * (1 - w) / (2 * Real.sqrt 2 * uOf α) *
            (2 * l2 (fun i => μ i - ν i) + l2 (fun i => (μt i - νt i) - (μ i - ν i))) *
            l2 (fun i => (μt i - νt i) - (μ i - ν i)) := by sorry

end PrefixMixLearn.Proper
