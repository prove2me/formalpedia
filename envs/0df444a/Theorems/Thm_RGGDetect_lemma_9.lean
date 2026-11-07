-- Prove2me | Theorems.Thm_RGGDetect_lemma_9
-- name    : RGGDetect.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:19.618013+00:00
-- url     : https://prove2.me/theorems/8801796b-a5c7-49a4-9d7f-775ea170075d
-- title:
--   Lemma 9 — harmonic expansion of $\eta_{D,S}$ with bounds (64)–(65)
-- statement:
--   Let $D\in\mathcal H_{\boldsymbol\ell}$ be nonzero, $u\in V$, $h=\ell_u$, and fix integers $k,M\ge1$. For any $S\subset V^c$ with $|S|=k$, $\eta_{D,S}$ of (45) has the orthogonal truncation
--
--   $$
--   \eta_{D,S}=\sum_{\mathbf a\in\mathcal A_{k,M}(h)}\gamma_{h;\mathbf a}\,(T^{u,S}_{\mathbf a}D)(x_{V\setminus\{u\}},x_S)+R_{D,S,M}, \tag{62}
--   $$
--
--   with $\mathcal A_{k,M}(h)=\{\mathbf a\in\mathbb N^k:q(h;\mathbf a)\le M\text{ and }\mathbf a\text{ satisfies (59)}\}$ (63). There are constants $C_0,C>0$ depending only on $h,k,M$ such that if $d\ge4$ and $0<p\le e^{-1}$, then for every $\mathbf a\in\mathcal A_{k,M}(h)$
--
--   $$
--   (\gamma_{h;\mathbf a})^2\le C\frac{p^kL^{\|\mathbf a\|_1}}{d^h},\qquad\mathbb E[(T^{u,S}_{\mathbf a}D)^2]\le C\frac{\mathbb E(D^2)}{d^s}, \tag{64}
--   $$
--
--   $s=(\|\mathbf a\|_1-h)/2$. If in addition $d\ge C_0L^2$, then
--
--   $$
--   \mathbb E[(R_{D,S,M})^2]\le C\,\mathbb E(D^2)\frac{p^kL^{2M+2-h}}{d^{M+1}}. \tag{65}
--   $$
--
--   The expectations are under the independent uniform prior on the arguments of each integrand.
--
--   **Formalization Note** $R_{D,S,M}$ is $\eta_{D,S}$ minus the main term. "Orthogonal truncation" is stated as: for every fixed configuration, the remainder as a function of $x_S$ is $L^2$-orthogonal to every $\mathcal H_{\mathbf a}$ with $\mathbf a$ positive on $S$ and $q(h;\mathbf a)\le M$; this part needs only $d\ge2$ and $0<p<1$. Multidegrees on $S$ are functions positive on $S$. The exponent $2M+2-h$ is an integer.
--
--   Differences from the source:
--   - encoding: R_{D,S,M} and 'orthogonal truncation' → R := η_{D,S} − main term; orthogonality to H_a (a positive on S, q(h;a) ≤ M) in x_S for every fixed configuration; reason: the paper's meaning of (62) (pp.19–20, 37: the main term is the orthogonal projection)
--   - encoding: (62) for the paper's d → d ≥ 2 and 0 < p < 1 for the orthogonality conjunct; reason: P_{ℓ,d} needs d ≥ 2 and κ needs 0 < p < 1
--   - encoding: a ∈ ℕ^k on x_S → a function positive on S, 0 off S; reason: indexing through an ordering of S
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 9, eqs. (62)–(65), pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_RGGDetect_harmCoef

open MeasureTheory

namespace RGGDetect

/-- **Lemma 9** (harmonic expansion of `η_{D,S}`; arXiv:2610.08517, held version, sha256 e7bebd4a…,
Lemma 9, pp.19–20, eqs. (62)–(65)): let `D ∈ H_ℓ` be nonzero, `u ∈ V`, `h = ℓ_u`, and fix integers
`k, M ≥ 1`. For any `S ⊂ V^c` with `|S| = k`, `η_{D,S}` has the orthogonal truncation
`η_{D,S} = ∑_{a ∈ A_{k,M}(h)} γ_{h;a} (T^{u,S}_a D)(x_{V∖u}, x_S) + R_{D,S,M}` (62), with
`A_{k,M}(h) = {a ∈ ℕ^k : q(h;a) ≤ M, a satisfies (59)}` (63). There are constants `C₀, C > 0`
depending only on `h, k, M` such that if `d ≥ 4` and `0 < p ≤ e^{-1}`, then for any `a ∈ A_{k,M}(h)`,
`(γ_{h;a})² ≤ C p^k L^{‖a‖₁}/d^h` and `E[(T^{u,S}_a D)²] ≤ C E(D²)/d^s`, `s = (‖a‖₁ - h)/2` (64);
if in addition `d ≥ C₀L²`, then `E[(R_{D,S,M})²] ≤ C E(D²) p^k L^{2M+2-h}/d^{M+1}` (65).

**Formalization Note** `R_{D,S,M}` is defined as `η_{D,S}` minus the main term (`remDS`), and
"orthogonal truncation" is the first conjunct: for every fixed configuration `x`, the remainder, as a
function of `x_S` (the other coordinates held at `x`), is `L²`-orthogonal to every `H_a` with `a`
positive on `S` and `q(h; a) ≤ M`. That conjunct needs only `d ≥ 2` and `0 < p < 1`. `a` is indexed by
`S` (positive on `S`, `0` off `S`), an encoding of `ℕ^k` through an ordering of `S`. Expectations are
under the product prior. The exponent `2M + 2 - h` is an integer. -/
theorem lemma_9 :
    (∀ n d : ℕ, 2 ≤ d → ∀ τ : ℝ, 0 < capProb d τ → capProb d τ < 1 →
      ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ), (∀ v ∈ V, 1 ≤ ℓ v) →
      ∀ D : Config n d → ℝ, D ∈ tensorHarm V ℓ → D ≠ 0 → ∀ u ∈ V, ∀ M : ℕ, 1 ≤ M →
      ∀ S : Finset (Fin n), Disjoint S V → 1 ≤ S.card →
      ∀ a : Fin n → ℕ, (∀ i ∈ S, 1 ≤ a i) → qHA (ℓ u) S a ≤ M →
      ∀ F : Config n d → ℝ, F ∈ tensorHarm S a → ∀ x : Config n d,
        ∫ y, remDS d τ (ℓ u) u S M D (fun i => if i ∈ S then y i else x i) * F y
          ∂(prior n d) = 0) ∧
    (∀ h k M : ℕ, 1 ≤ k → 1 ≤ M → ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
      ∀ n d : ℕ, 4 ≤ d → ∀ τ : ℝ, 0 < capProb d τ → capProb d τ ≤ Real.exp (-1) →
      ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ), (∀ v ∈ V, 1 ≤ ℓ v) →
      ∀ D : Config n d → ℝ, D ∈ tensorHarm V ℓ → D ≠ 0 → ∀ u ∈ V, ℓ u = h →
      ∀ S : Finset (Fin n), Disjoint S V → S.card = k →
        (∀ a ∈ multiIdx S M h,
          gammaHA d τ h S a ^ 2 ≤
              C * capProb d τ ^ k * Real.log (1 / capProb d τ) ^ (∑ i ∈ S, a i) / (d : ℝ) ^ h ∧
          ∫ x, opT d h u S a D x ^ 2 ∂(prior n d) ≤
              C * (∫ x, D x ^ 2 ∂(prior n d)) /
                (d : ℝ) ^ (((∑ i ∈ S, a i : ℕ) - (h : ℝ)) / 2)) ∧
        (C₀ * Real.log (1 / capProb d τ) ^ 2 ≤ d →
          ∫ x, remDS d τ h u S M D x ^ 2 ∂(prior n d) ≤
            C * (∫ x, D x ^ 2 ∂(prior n d)) * capProb d τ ^ k *
              Real.log (1 / capProb d τ) ^ ((2 * M + 2 : ℤ) - h) / (d : ℝ) ^ (M + 1))) := by sorry

end RGGDetect
