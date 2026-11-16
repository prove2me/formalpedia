-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_lemma_17
-- name    : TwoOptAllExp.TSP.Supplement.lemma_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T04:47:11.58337+00:00
-- url     : https://prove2.me/theorems/5bfdef7c-6bb2-4da8-a189-ca4c29e6bf44
-- title:
--   Lemma 17 — AND-NOT, OR and tie-breaker vertices
-- statement:
--   Let $D>0$ and let $z$ be a vertex whose neighbors are $x\neq y$ and possibly one further neighbor $t$. Let $r=w(zt)(1-2\sigma(t))$ if $t$ exists and $r=0$ otherwise, and suppose $|r|<D$.
--
--   1. (AND-NOT) If $w(zx)=-D$, $w(zy)=+D$, $b_z=-D$, then $\Delta_z=2D(\sigma(x)-\sigma(y))-D+r$, which equals $D+r$ if $(\sigma(x),\sigma(y))=(1,0)$ and is at most $-D+r$ otherwise; hence $z\leftarrow x\wedge\bar y$.
--   2. (OR) If $w(zx)=w(zy)=-D$ and $b_z=+D$, then $\Delta_z=2D(\sigma(x)+\sigma(y))-D+r$; hence $z\leftarrow x\vee y$.
--   3. (tie breaker) Suppose $t$ exists. If $w(zx)=w(zy)=-D$ and $b_z=0$, then $$\Delta_z=2D(\sigma(x)+\sigma(y)-1)+r.$$ Hence $z\leftarrow x$ on assignments with $\sigma(x)=\sigma(y)$; on assignments with $\sigma(x)\ne\sigma(y)$, $z\leftarrow\bar t$ if $w(zt)>0$ and $z\leftarrow t$ if $w(zt)<0$.
--
--   These are the Boolean gates of the Section 5 gadgets.
--
--   Differences from the source:
--   - encoding: z has neighbors x, y and possibly another neighbor t → t : Option V; the neighbors of z are exactly x, y and (if t = some t₀) t₀, with x ≠ y and t₀ ∉ {x, y}; reason: makes "possibly another" precise
--   - encoding: suppose |r| < D → ∀ σ, |r(σ)| < D; reason: |r| equals |w(zt)| (or 0) for every σ, so this is the same condition
--   - encoding: suppose t exists → ∀ t₀, t = some t₀ → …; reason: naming the existing neighbor
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 17, p. 26

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_GraphObjective

namespace TwoOptAllExp.TSP.Supplement

/-- **Lemma 17** (p. 26). Let `D > 0`, let `z` have neighbors `x, y` and possibly another neighbor
`t` (`t = none`: no further neighbor). Let `r = w(zt)(1 - 2σ(t))` if `t` exists and `0` otherwise,
and suppose `|r| < D`.
(i) (AND-NOT) If `w(zx) = -D`, `w(zy) = +D`, `b_z = -D`, then `Δ_z = 2D(σ(x) - σ(y)) - D + r`, which is
`D + r` if `(σ(x), σ(y)) = (1, 0)` and at most `-D + r` otherwise; hence `z ← x ∧ ȳ`.
(ii) (OR) If `w(zx) = w(zy) = -D` and `b_z = +D`, then `Δ_z = 2D(σ(x) + σ(y)) - D + r`; hence `z ← x ∨ y`.
(iii) (tie breaker) Suppose `t` exists. If `w(zx) = w(zy) = -D` and `b_z = 0`, then
`Δ_z = 2D(σ(x) + σ(y) - 1) + r`. Hence `z ← x` on assignments with `σ(x) = σ(y)`; on assignments
with `σ(x) ≠ σ(y)`, `z ← t̄` if `w(zt) > 0` and `z ← t` if `w(zt) < 0`. -/
theorem lemma_17 {V : Type} [Fintype V] [DecidableEq V] (W : WGraph V) (D : ℤ) (hD : 0 < D)
    (z x y : V) (t : Option V) (hxy : x ≠ y) (htx : t ≠ some x) (hty : t ≠ some y)
    (hnbr : ∀ u : V, W.G.Adj z u ↔ (u = x ∨ u = y ∨ t = some u))
    (hr : ∀ σ : V → Bool, |W.tieTerm z t σ| < D) :
    (W.w s(z, x) = -D → W.w s(z, y) = D → W.b z = -D →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) - b2i (σ y)) - D + W.tieTerm z t σ ∧
        ((σ x = true ∧ σ y = false) → W.Δ z σ = D + W.tieTerm z t σ) ∧
        (¬ (σ x = true ∧ σ y = false) → W.Δ z σ ≤ -D + W.tieTerm z t σ)) ∧
      W.Follows z (fun σ => σ x && !σ y)) ∧
    (W.w s(z, x) = -D → W.w s(z, y) = -D → W.b z = D →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y)) - D + W.tieTerm z t σ) ∧
      W.Follows z (fun σ => σ x || σ y)) ∧
    (∀ t₀ : V, t = some t₀ → W.w s(z, x) = -D → W.w s(z, y) = -D → W.b z = 0 →
      (∀ σ : V → Bool,
        W.Δ z σ = 2 * D * (b2i (σ x) + b2i (σ y) - 1) + W.tieTerm z t σ) ∧
      W.FollowsOn z (fun σ => σ x) {σ | σ x = σ y} ∧
      (0 < W.w s(z, t₀) → W.FollowsOn z (fun σ => !σ t₀) {σ | σ x ≠ σ y}) ∧
      (W.w s(z, t₀) < 0 → W.FollowsOn z (fun σ => σ t₀) {σ | σ x ≠ σ y})) := by sorry

end TwoOptAllExp.TSP.Supplement
