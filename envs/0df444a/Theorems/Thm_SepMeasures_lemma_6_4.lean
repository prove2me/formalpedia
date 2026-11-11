-- Prove2me | Theorems.Thm_SepMeasures_lemma_6_4
-- name    : SepMeasures.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:50.187646+00:00
-- url     : https://prove2.me/theorems/4f226099-5d9f-4203-acfb-b7bcf3a9f9f0
-- title:
--   Lemma 6.4 — tilting a hyperplane off one small ball
-- statement:
--   Let $d\ge1$, let $x_1,\dots,x_n\in\mathbb R^d$ be distinct points in affine general position, and let $K\subset\mathbb R^d$ be bounded. For every $\varepsilon>0$ there are $r_\varepsilon>0$ and $C_\varepsilon<\infty$ such that the following holds whenever $0<r<r_\varepsilon$. Let $B_i=B(x_i,r)$ be the closed Euclidean balls, let $H$ be a hyperplane and $i_0$ an index with $H\cap B_{i_0}\neq\emptyset$, and let $\sigma\in\{+,-\}$. Then there is a hyperplane $\tilde H$ such that
--   1. $\tilde H$ intersects no ball that $H$ does not intersect;
--   2. $\tilde H\cap B_{i_0}=\emptyset$ and $B_{i_0}\subseteq\tilde H^\sigma$;
--   3. for every $i\neq i_0$, $$\frac{\mathrm{Leb}\big(B_i\cap(H^+\,\triangle\,\tilde H^+)\big)}{\mathrm{Leb}(B_i)}<\varepsilon;$$
--   4. every $x\in K$ that does not lie in the same open half-space of $H$ and of $\tilde H$ (that is, $\sigma_H(x)\,\sigma_{\tilde H}(x)\le0$) satisfies $\operatorname{dist}(x,H)\le C_\varepsilon r$.
--
--   The lemma is the rounding step of Lemma 6.2: a hyperplane that cuts the small ball around an atom can be moved off it, without cutting new balls and while changing the cut value only slightly.
--
--   **Formalization Note** Balls, $\mathrm{Leb}$ (`volume`) and $\operatorname{dist}(\cdot,H)$ are Euclidean; the orientation of $\tilde H$ is part of the existential, and (b), (c) refer to it.
--
--   Differences from the source:
--   - reading: x₁, …, xₙ ∈ ℝ^d in affine general position → an injective family x : Fin n → ℝ^d whose range is in affine general position; reason: a list with a repeated point is not affinely independent as a family, and the paper applies the lemma to distinct atoms
--   - generalization: (d): every x ∈ K that lies in different open half-spaces determined by H and H̃ → every y ∈ K with σ_H(y) σ_H̃(y) ≤ 0 (which also covers points on H or on H̃); reason: the proof on p.50 establishes this form ("either … opposite signs or one vanishes"); it implies the printed one
--   - encoding: σ ∈ {+, −}; C_ε < ∞; the ratio Leb(·)/Leb(B_i) → σ : Bool (true = +); C_ε : ℝ; the ratio of volumes in ℝ≥0∞, compared with ENNReal.ofReal ε; reason: a closed ball of positive radius has positive finite volume, so the ratio is the paper's
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Lemma 6.4, p.48 (proof pp.48–50)

import Mathlib
import Definitions.Def_SepMeasures_Families

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Lemma 6.4, p.48 (proof pp.48–50): let `x₁, …, xₙ ∈ ℝ^d`
be in affine general position and `K ⊂ ℝ^d` bounded. For every `ε > 0` there are `r_ε > 0` and
`C_ε < ∞` such that, whenever `0 < r < r_ε`, for `Bᵢ := B(xᵢ, r)`, every hyperplane `H` and every
`i₀` with `H ∩ B_{i₀} ≠ ∅`, and each `σ ∈ {+, −}`, there is a hyperplane `H̃` with
(a) `H̃` intersects no ball that `H` did not intersect;
(b) `H̃ ∩ B_{i₀} = ∅` and `B_{i₀} ⊆ H̃^σ`;
(c) `Leb(Bᵢ ∩ (H⁺ △ H̃⁺)) / Leb(Bᵢ) < ε` for every `i ≠ i₀`;
(d) every `x ∈ K` in different open half-spaces of `H` and `H̃` has `dist(x, H) ≤ C_ε r`.

**Formalization Note.** The points are an injective family `x : Fin n → ℝ^d` (distinct points,
as in the paper's application to distinct atoms). Balls, `Leb` (`volume`) and `dist(·, H)` are
Euclidean. `σ = true` is `+` and `σ = false` is `−`. In (d), "in different open half-spaces"
is encoded as `σ_H(y) σ_{H̃}(y) ≤ 0`, which also covers points on `H` or on `H̃` (the form the
proof on p.50 establishes) and implies the printed reading. -/
theorem lemma_6_4 (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (x : Fin n → E d) (hinj : Function.Injective x)
    (hgen : AffGenPos d (Set.range x)) (K : Set (E d)) (hK : Bornology.IsBounded K) :
    ∀ ε : ℝ, 0 < ε → ∃ rε : ℝ, 0 < rε ∧ ∃ Cε : ℝ, ∀ r : ℝ, 0 < r → r < rε →
      ∀ H : Hyp d, ∀ i₀ : Fin n, (H.set ∩ Metric.closedBall (x i₀) r).Nonempty →
        ∀ σ : Bool, ∃ H' : Hyp d,
          (∀ i, (H'.set ∩ Metric.closedBall (x i) r).Nonempty →
              (H.set ∩ Metric.closedBall (x i) r).Nonempty) ∧
          (H'.set ∩ Metric.closedBall (x i₀) r = ∅ ∧
              Metric.closedBall (x i₀) r ⊆ (if σ then H'.pos else H'.neg)) ∧
          (∀ i, i ≠ i₀ →
              volume (Metric.closedBall (x i) r ∩ symmDiff H.pos H'.pos) /
                volume (Metric.closedBall (x i) r) < ENNReal.ofReal ε) ∧
          (∀ y ∈ K, H.sign y * H'.sign y ≤ 0 → Metric.infDist y H.set ≤ Cε * r) := by sorry

end SepMeasures
