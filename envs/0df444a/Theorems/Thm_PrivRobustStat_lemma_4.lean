-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_4
-- name    : PrivRobustStat.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:25.655552+00:00
-- url     : https://prove2.me/theorems/82e2639c-9ae3-493a-81fd-42d133838e3b
-- title:
--   Lemma 4, p.18 — PrivateMultiply is $(\lambda,2R^2\omega^2/(n^2\sigma^2))$-RDP under Property 1 and (9)
-- statement:
--   **Lemma 4** (privacy of PrivateMultiply). Let $c\in\mathbb R^d$, $R>0$, $V\in\mathbb R^{d\times r}$, $\omega,\sigma>0$, and let the weights be $w_i=f_i(x_i)$ for public $f_i:\mathbb R^d\to[0,\tfrac1n]$ (Property 1). Then for every $\lambda>1$ the output $Y$ of Algorithm 2 is
--
--   $$\Big(\lambda,\frac{2R^2\omega^2}{n^2\sigma^2}\Big)\text{-RDP}$$
--
--   over neighbouring datasets that both satisfy (9): $\|x_i-c\|_2\le R$ for all $i$.
--
--   Differences from the source:
--   - encoding: input weights satisfying Property 1 → w_i = f_i(x_i) for public weight functions f_i : ℝ^d → [0, 1/n] fixed before the dataset; reason: Property 1 with the preceding query history public
--   - encoding: "(9) holds" → RDP over neighbouring datasets that both satisfy (9); reason: (9) is a condition on the dataset, so it is imposed on both neighbours
--   - encoding: the output law of the mechanism → the law is the pushforward of the noise measure, and the item also asserts the output map is measurable; reason: Lean pushes a non-measurable map to the zero measure, under which privacy would hold vacuously; measurability rules this out and changes no instance
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 4, p.18 (PDF p.21); (9), p.15; Algorithm 2, p.17

import Mathlib
import Definitions.Def_PrivRobustStat_Privacy
import Definitions.Def_PrivRobustStat_Filter

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 4** (privacy of `PrivateMultiply`), p.18 (PDF p.21).

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Suppose that the input w to Algorithm 2 satisfies Property 1, and that (9) holds. Then the output Y
of Algorithm 2 satisfies (λ, 2R²ω²/(n²σ²))-RDP for every λ > 1."

(9), p.15: `∥x_i − c∥₂ ≤ R for all i ∈ [n]`, for some `R > 0`.

**Formalization Note.** Property 1: the weights are `w_i := f i (x_i)` for public weight functions
`f i : ℝ^d → [0, 1/n]` fixed before the dataset. The centre `c`, `V ∈ ℝ^{d×r}`, `ω, σ > 0` are
public. The mechanism maps the dataset `x[n]` to the law of `Y` under the standard Gaussian matrix
`G` (`stdGauss (Fin d × Fin r)`); RDP is over neighbouring datasets that both satisfy (9). The
first conjunct says the output is a measurable function of `G`, so the law is the genuine
pushforward. -/
theorem lemma_4 {d n r : ℕ} (c : Vec d) (R : ℝ) (hR : 0 < R) (f : Fin n → Vec d → ℝ)
    (hf : IsWeightFn n f) (V : Matrix (Fin d) (Fin r) ℝ) (ω σ : ℝ) (hω : 0 < ω) (hσ : 0 < σ) :
    (∀ x : Fin n → Vec d, Measurable fun G : Fin d × Fin r → ℝ =>
      fun a b => privMultiply x c (fun i => f i (x i)) V ω σ (Matrix.of fun a b => G (a, b)) a b) ∧
    ∀ lam : ℝ, 1 < lam →
      IsRDPOn (fun x : Fin n → Vec d => ∀ i, ‖x i - c‖ ≤ R) lam
        (2 * R ^ 2 * ω ^ 2 / ((n : ℝ) ^ 2 * σ ^ 2))
        (fun x => (stdGauss (Fin d × Fin r)).map fun G =>
          fun a b => privMultiply x c (fun i => f i (x i)) V ω σ (Matrix.of fun a b => G (a, b)) a b) := by sorry

end PrivRobustStat
