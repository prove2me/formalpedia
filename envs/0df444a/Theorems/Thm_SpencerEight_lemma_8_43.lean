-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_43
-- name    : SpencerEight.lemma_8_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:32.962437+00:00
-- url     : https://prove2.me/theorems/1ff9a018-ce7e-4a6c-b09d-28fe5ae138c4
-- title:
--   Lemma 8.43 — moment constraints at every active size
-- statement:
--   Let $0<q<1$, $w,\eta,L>0$, $a,\beta,c,\theta\ge0$, $m\le wn$, and let $b$ be a nonnegative integer. For symmetric matrices $B_i$ put $G(x):=\sum_{i=1}^mx_iB_i$. Let $K_0$ be a symmetric convex Borel subset of the norm body $\{x:\|G(x)\|\le\sqrt{wn/\eta}\}$ with
--   $$\gamma_m[K_0]\ge\exp[-m(a/w+\beta/2)-\theta],$$
--   and let $K_1,\dots,K_b\subseteq\mathbb R^m$ be symmetric convex Borel sets of Gaussian mass at least $e^{-c}$. If
--   $$L^2s_+^2\eta\ge w,\qquad n\bigl(w(d_8(q)-\beta/2)-a\bigr)>cb+\theta,$$
--   then there is $y\in\{-1,0,1\}^m$ with $\|G(y)\|\le L\sqrt n$, $s_+y\in\bigcap_{r=0}^bK_r$, and at most $qwn$ zero coordinates. If $m\le qwn$, one may take $y=0$.
--
--   The lemma imposes moment bodies on a partial signing, and it allows a phase to be skipped when few coefficients remain.
--
--   Differences from the source:
--   - generalization: matrix dimension unstated (n × n in the applications) → matrices indexed by an arbitrary finite type d; reason: the lemma uses n only through m ≤ wn and the radii; d = Fin n is the source's case
--   - encoding: K₀, K₁, …, K_b → K : Fin (b + 1) → Set (Fin m → ℝ); reason: indexing only
--   - encoding: one may take y = 0 → y = 0 satisfies the three conclusions on the norm, the sets and the zero count when m ≤ qwn; reason: that is what taking y = 0 asserts
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.43, p.105 (PDF p.105)

import Mathlib
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_signedSum
import Definitions.Def_SpencerEight_sPlus
import Definitions.Def_SpencerEight_d8
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- Lemma 8.43 (Moment constraints at every active size), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.105 (PDF p.105).

**Formalization Note** `K 0` is `K₀`; `K r`, `r = 1, …, b`, are `K₁, …, K_b`. `d` is an arbitrary finite index type of the matrices, because the lemma leaves the matrix dimension unstated and uses `n` only through `m ≤ wn` and the radii. -/
theorem lemma_8_43 {d : Type*} [Fintype d] [DecidableEq d] {n m b : ℕ}
    {q w η L a β c θ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hw : 0 < w) (hη : 0 < η) (hL : 0 < L)
    (ha : 0 ≤ a) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hθ : 0 ≤ θ) (hm : (m : ℝ) ≤ w * n)
    (B : Fin m → Matrix d d ℝ) (hB : ∀ i, (B i).IsSymm)
    (K : Fin (b + 1) → Set (Fin m → ℝ))
    (hKB : ∀ r, MeasurableSet (K r)) (hKc : ∀ r, Convex ℝ (K r)) (hKs : ∀ r, ∀ x ∈ K r, -x ∈ K r)
    (hK0 : K 0 ⊆ {x | ‖signedSum B x‖ ≤ Real.sqrt (w * n / η)})
    (hK0m : ENNReal.ofReal (Real.exp (-((m : ℝ) * (a / w + β / 2)) - θ)) ≤ gammaM (Fin m) (K 0))
    (hKr : ∀ r : Fin (b + 1), r ≠ 0 → ENNReal.ofReal (Real.exp (-c)) ≤ gammaM (Fin m) (K r))
    (hrad : w ≤ L ^ 2 * sPlus ^ 2 * η)
    (hres : c * b + θ < (n : ℝ) * (w * (d8 q - β / 2) - a)) :
    (∃ y : Fin m → ℝ, (∀ i, y i = -1 ∨ y i = 0 ∨ y i = 1) ∧
      ‖signedSum B y‖ ≤ L * Real.sqrt n ∧
      (∀ r, sPlus • y ∈ K r) ∧
      ((Finset.univ.filter fun i => y i = 0).card : ℝ) ≤ q * w * n) ∧
    ((m : ℝ) ≤ q * w * n →
      ‖signedSum B (0 : Fin m → ℝ)‖ ≤ L * Real.sqrt n ∧
      (∀ r, sPlus • (0 : Fin m → ℝ) ∈ K r) ∧
      ((Finset.univ.filter fun i : Fin m => (0 : Fin m → ℝ) i = 0).card : ℝ) ≤ q * w * n) := by sorry

end SpencerEight
