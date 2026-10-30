-- Prove2me | Theorems.Thm_PorteusGenSS_lemma_2_value_subadditive
-- name    : PorteusGenSS.lemma_2_value_subadditive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:18:28.054728+00:00
-- url     : https://prove2.me/theorems/6e5ab829-a749-48b9-8c5f-8329732e0ec8
-- title:
--   Lemma 2: $f_n(x)\le f_n(y)+c(y-x)$
-- statement:
--   Let $c$ be concave and nondecreasing on $[0,\infty)$ with $c(0)=0$, let $h:\mathbb R\to\mathbb R$ be any function and
--
--   $$
--   f(x)=\inf_{w\ge x}\{c(w-x)+h(w)\}.
--   $$
--
--   Let $x\le y$ and assume $f(x)>-\infty$. Then
--
--   1. $f(x)\le f(y)+c(y-x)$, and
--   2. for every slope $a\in C$ with intercept $K_a$: $f(x)\le f(y)+a\,(y-x)+K_a$; that is, $f+a\cdot$ is non-$K_a$-decreasing.
--
--   With $h=h_n$ this is the paper's statement for $f_n$, $n\ge1$. It reflects the subadditivity of a concave ordering cost.
--
--   Differences from the source:
--
--   - generalization: fn = inf_{y≥x}{c(y − x) + hn(y)} with hn = (m + αfn−1)∗φ, n ≥ 1 → valueOp c h for an arbitrary h : ℝ → ℝ; reason: hn is one such h; the proof uses only the subadditivity of c
--   - generalization: the §II standing assumption that lim C2(z) exists at 0 and ∞ → not assumed; reason: the statement for every c is in particular the statement for those c
--   - encoding: fn(x) ∈ [−∞, ∞) (an infimum) → BddBelow of {c(w − x) + h(w) : w ≥ x}; reason: excludes only fn(x) = −∞, where the paper's inequality is trivially true; needed because Lean's real ⨅ is 0 on sets unbounded below
--   - reading: c concave increasing → ConcaveOn and MonotoneOn on [0, ∞) (nondecreasing); reason: the paper never defines "increasing"; nondecreasing is the weaker hypothesis, so the theorem covers every strictly increasing c as well
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Lemma 2, p. 418

import Mathlib
import Definitions.Def_PorteusGenSS_IsOrderingCost
import Definitions.Def_PorteusGenSS_IsTangentPair
import Definitions.Def_PorteusGenSS_valueOp

namespace PorteusGenSS

/-- **Lemma 2 (fₙ(x) ≤ fₙ(y) + c(y − x), and fₙ + c· is non-K_c-decreasing).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Lemma 2, p. 418:
"If x ≤ y and n ≥ 1, then fn(x) ≤ fn(y) + c(y − x). Note that, in particular, if x ≤ y then
fn(x) ≤ fn(y) + c·(y − x) + Kc for c ∈ C. That is, fn + c· is non-Kc-decreasing on R for c ∈ C."

For a concave nondecreasing `c` on `[0, ∞)` with `c(0) = 0`, any function `h`, and
`f(x) = inf_{w ≥ x} (c(w − x) + h(w))`: if `x ≤ y` and `f(x) > −∞`, then
`f(x) ≤ f(y) + c(y − x)` and `f(x) ≤ f(y) + a(y − x) + K` for every slope `a ∈ C` with its
intercept `K = K_a`.

**Formalization Note.** `h` is arbitrary (the paper's `fₙ` is `valueOp c hₙ`); the proof uses
only the subadditivity of `c`. The hypothesis `hbdd` (the infimum defining `f(x)` is finite)
excludes only `f(x) = −∞`, where the paper's inequality holds trivially; it is needed because
the real `⨅` takes the value `0` on sets unbounded below. It implies the same at `y`. The limits
`(c₀, K₀)`, `(c_∞, K_∞)` of §II are not assumed. -/
theorem lemma_2_value_subadditive {c h : ℝ → ℝ} (hc : IsOrderingCost c) {x y : ℝ} (hxy : x ≤ y)
    (hbdd : BddBelow (Set.range fun w : Set.Ici x => c ((w : ℝ) - x) + h w)) :
    valueOp c h x ≤ valueOp c h y + c (y - x) ∧
      ∀ a K : ℝ, IsTangentPair c a K → valueOp c h x ≤ valueOp c h y + a * (y - x) + K := by sorry

end PorteusGenSS
