-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_lemma_B_15
-- name    : ProcessingNetworks.EntropyIneq.lemma_B_15
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:28:04.354464+00:00
-- url     : https://prove2.me/theorems/3fe24f80-e4a0-4e12-a8b7-06b8f271ebe1
-- title:
--   Lemma B.15 — $x\log x$: right-continuous at $0$, negative on $(0,1)$, $\inf_{x\ge0}x\log x=-1/e$
-- statement:
--   Let $h:\mathbb R_+\to\mathbb R$, $h(x)=x\log x$, with the convention $0\log0=0$ (10.46). Then
--
--   1. $h$ is right continuous at $x=0$;
--   2. $h(x)<0$ for every $x\in(0,1)$;
--   3. $$\inf_{x\ge0}x\log x=-\frac1e .$$
--
--   This elementary fact bounds the entropy-like terms $d\log d$ from below in the Lyapunov analysis of Chapter 10 and in Lemma B.16.
--
--   **Formalization Note** Right continuity at $0$ of a function on $\mathbb R_+$ is continuity within $[0,\infty)$ at $0$. The infimum is stated as "$-1/e$ is the greatest lower bound of $\{x\log x: x\ge0\}$", so no default value of an infimum operator can satisfy it vacuously.
--
--   Differences from the source:
--
--   - encoding: inf_{x≥0} x log(x) = −1/e → IsGLB {x log x | x ≥ 0} (−(1/e)); reason: the same statement; avoids sInf junk values
--   - encoding: convention 0 log 0 = 0 (10.46) → Real.log 0 = 0, so 0 * Real.log 0 = 0; reason: Lean's logarithm already has this value
--   - encoding: h is right continuous at x = 0 → ContinuousWithinAt h (Set.Ici 0) 0; reason: h is a function on ℝ₊, so right continuity at 0 is continuity within [0, ∞)
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix B §B.4, Lemma B.15, eq. (B.34), p.273 (PDF 289)

import Mathlib

namespace ProcessingNetworks.EntropyIneq

/-- **Lemma B.15** (Dai & Harrison, *Processing Networks*, pre-publication draft 2020-4-2,
spnbook.org, Appendix B §B.4, Lemma B.15, eq. (B.34), p.273 (PDF 289)). The function
`h : x ∈ ℝ₊ ↦ h(x) = x log(x) ∈ ℝ` (with the convention `0 log 0 = 0`, (10.46)) is right continuous
at `x = 0`, is strictly negative in `(0, 1)`, and satisfies `inf_{x ≥ 0} x log(x) = −1/e`.

**Formalization Note** `Real.log 0 = 0`, so `0 * Real.log 0 = 0` is the convention (10.46).
Right continuity at `0` of a function on `ℝ₊` is continuity within `[0, ∞)` at `0`. The infimum is
stated as `IsGLB` of the image of `[0, ∞)`, so no junk value of `sInf` can satisfy it; `e` is
`Real.exp 1`. -/
theorem lemma_B_15 :
    ContinuousWithinAt (fun x : ℝ => x * Real.log x) (Set.Ici 0) 0 ∧
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, x * Real.log x < 0) ∧
      IsGLB ((fun x : ℝ => x * Real.log x) '' Set.Ici 0) (-(1 / Real.exp 1)) := by sorry

end ProcessingNetworks.EntropyIneq
