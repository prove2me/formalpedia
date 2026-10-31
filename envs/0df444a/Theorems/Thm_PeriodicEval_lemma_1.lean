-- Prove2me | Theorems.Thm_PeriodicEval_lemma_1
-- name    : PeriodicEval.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:06:55.454343+00:00
-- url     : https://prove2.me/theorems/a1cd6492-9294-4067-902a-6f45b773b765
-- title:
--   Lemma 1 — shape of $G_a$ in four regimes of $a$
-- statement:
--   Let $G_a(y)=U(y-\gamma)+ay^\alpha$, $y\ge0$, under the standing assumptions. Write $b_1=\gamma/(1+(k/a)^{1/(2-\alpha)})$, $b=\gamma/(1+(k/|a|)^{1/(1-\alpha)})$, $b_4=\gamma/(1-|a|^{-1/(1-\alpha)})$, $b_5=\gamma/(1-|a|^{-1/(2-\alpha)})$ and $\kappa=(k^{1/(1-\alpha)}+1)^{1-\alpha}$.
--
--   1. For $a>0$, $G_a$ is concave increasing on $[0,b_1]$, convex increasing on $(b_1,\gamma]$ and concave increasing on $(\gamma,\infty)$.
--   2. For $a=0$, $G_a$ is convex increasing on $[0,\gamma]$ and concave increasing on $(\gamma,\infty)$.
--   3. For $-1\le a<0$, $G_a$ is convex decreasing on $[0,b]$, convex increasing on $(b,\gamma]$ and concave increasing on $(\gamma,\infty)$.
--   4. For $a<-1$, $G_a$ is convex decreasing on $[0,b]$, convex increasing on $(b,\gamma]$, concave increasing on $(\gamma,b_4]$, concave decreasing on $(b_4,b_5]$ and convex decreasing on $(b_5,\infty)$. Moreover
--      (a) if $-\kappa<a<-1$, $G_a$ attains its global maximum over $[0,\infty)$ at $y=b_4$;
--      (b) if $a<-\kappa$, $G_a$ attains its global maximum over $[0,\infty)$ at $y=0$.
--
--   The lemma describes the non-concave reward that the concavification of Lemma 2 smooths out.
--
--   **Formalization Note** "Concave increasing on $I$" is concavity on $I$ together with monotonicity on $I$.
--
--   Differences from the source:
--   - reading: increasing / decreasing → MonotoneOn / AntitoneOn (non-strict); reason: at a = 0 and k = 0, G_0 is constant on [0, γ], so the strict reading of case 2 is false; elsewhere the non-strict reading is the paper's claim
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), Lemma 1, pp.32–33

import Mathlib
import Definitions.Def_PeriodicEval_Utility

open Set

namespace PeriodicEval

/-- Lemma 1, SSRN 3971852 (June 20, 2023), pp.32–33: the shape of `G_a(y) = U(y − γ) + a y^α`
on `y ≥ 0`, in four regimes of `a`, and the location of its global maximum for `a < −1`.
"Concave/convex increasing/decreasing on an interval" is `ConcaveOn`/`ConvexOn` together with
`MonotoneOn`/`AntitoneOn` on that interval, with the interval endpoints as printed.

**Formalization Note** The standing assumptions (`Params.Standing`) are hypotheses. -/
theorem lemma_1 (p : Params) (hp : p.Standing) :
    -- 1. a > 0
    (∀ a : ℝ, 0 < a →
      let b := p.γ / (1 + (p.k / a) ^ (1 / (2 - p.α)))
      (ConcaveOn ℝ (Icc 0 b) (G p a) ∧ MonotoneOn (G p a) (Icc 0 b)) ∧
      (ConvexOn ℝ (Ioc b p.γ) (G p a) ∧ MonotoneOn (G p a) (Ioc b p.γ)) ∧
      (ConcaveOn ℝ (Ioi p.γ) (G p a) ∧ MonotoneOn (G p a) (Ioi p.γ))) ∧
    -- 2. a = 0
    ((ConvexOn ℝ (Icc 0 p.γ) (G p 0) ∧ MonotoneOn (G p 0) (Icc 0 p.γ)) ∧
      (ConcaveOn ℝ (Ioi p.γ) (G p 0) ∧ MonotoneOn (G p 0) (Ioi p.γ))) ∧
    -- 3. −1 ≤ a < 0
    (∀ a : ℝ, -1 ≤ a → a < 0 →
      let b := p.γ / (1 + (p.k / |a|) ^ (1 / (1 - p.α)))
      (ConvexOn ℝ (Icc 0 b) (G p a) ∧ AntitoneOn (G p a) (Icc 0 b)) ∧
      (ConvexOn ℝ (Ioc b p.γ) (G p a) ∧ MonotoneOn (G p a) (Ioc b p.γ)) ∧
      (ConcaveOn ℝ (Ioi p.γ) (G p a) ∧ MonotoneOn (G p a) (Ioi p.γ))) ∧
    -- 4. a < −1, with (a) and (b)
    (∀ a : ℝ, a < -1 →
      let b := p.γ / (1 + (p.k / |a|) ^ (1 / (1 - p.α)))
      let b₄ := p.γ / (1 - |a| ^ (-1 / (1 - p.α)))
      let b₅ := p.γ / (1 - |a| ^ (-1 / (2 - p.α)))
      ((ConvexOn ℝ (Icc 0 b) (G p a) ∧ AntitoneOn (G p a) (Icc 0 b)) ∧
        (ConvexOn ℝ (Ioc b p.γ) (G p a) ∧ MonotoneOn (G p a) (Ioc b p.γ)) ∧
        (ConcaveOn ℝ (Ioc p.γ b₄) (G p a) ∧ MonotoneOn (G p a) (Ioc p.γ b₄)) ∧
        (ConcaveOn ℝ (Ioc b₄ b₅) (G p a) ∧ AntitoneOn (G p a) (Ioc b₄ b₅)) ∧
        (ConvexOn ℝ (Ioi b₅) (G p a) ∧ AntitoneOn (G p a) (Ioi b₅))) ∧
      (-p.κ < a → IsMaxOn (G p a) (Ici 0) b₄) ∧
      (a < -p.κ → IsMaxOn (G p a) (Ici 0) 0)) := by sorry

end PeriodicEval
