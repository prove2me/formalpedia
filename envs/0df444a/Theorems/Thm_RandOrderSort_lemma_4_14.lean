-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_14
-- name    : RandOrderSort.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:57.766672+00:00
-- url     : https://prove2.me/theorems/03302000-f84c-4bd4-b00c-a33071e34be6
-- title:
--   Lemma 4.14 — witness decomposition and phase moments
-- statement:
--   For $n\ge 8192$ independent uniform inputs and a fixed $q\in(0,1)$, the nonnegative variables $G_j$, $D_{\mathrm{err}}$, $W_i$ of (40), (46) and (50) satisfy, on the probability-one event of distinct keys unequal to $q$,
--   $$C(q)\le D_1(L+k+1)+\sum_{j=0}^{L-1}G_j+D_{\mathrm{err}}+\sum_{i=1}^{k-1}W_i,\qquad D_1=7000.$$
--   At the common parameter $\theta=1/29360128$ the following moment bounds of Table 2 hold:
--   $$\mathbb E\bigl[e^{\theta\sum_jG_j}\bigm|P_L\bigr]\le M_g^L\ \text{a.s.},\qquad \mathbb E[e^{\theta D_{\mathrm{err}}}]\le M_b,\qquad \mathbb E\bigl[e^{\theta\sum_iW_i}\bigm|P_L\bigr]\le M_s^{k-1}\ \text{a.s.}$$
--   The growing and future-block sums are independent conditional on $P_L$.
--
--   This is the decomposition that Proposition 4.15 integrates.
--
--   **Formalization Note** $M_b$ is the constant of (52), and $M_s=1+2e^{-1/3}/(1-e^{-1/6})$ is that of the proof of Lemma 4.13. Conditioning is on $\sigma(P_L)$.
--
--   Differences from the source:
--   - generalization: (54) on the probability-one event of distinct keys unequal to q → for every input vector with distinct values none equal to q, not only those in [0,1]; reason: the deterministic inequality on the page's event is a special case
--   - encoding: the moment bounds in Table 2 at the common parameter θ → the explicit θ = 1/29360128 of (53) and the explicit M_g, M_b, M_s, with integrability stated; reason: Table 2 and displays (41), (52), p.35
--   - encoding: independent conditional on P_L → Mathlib's `CondIndepFun` given `HL n`; reason: the conditional independence of the two sums
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.14, p.36, display (54); Table 2, p.36; (52)–(53), p.36; M_s, p.35

import Mathlib
import Definitions.Def_RandOrderSort_Gj
import Definitions.Def_RandOrderSort_Wi
open MeasureTheory

namespace RandOrderSort

/-- **Lemma 4.14 (Witness decomposition and phase moments)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.36: "For n ≥ 8192 independent
uniform inputs and a fixed q ∈ (0, 1), the nonnegative variables G_j, D_err, W_i from (40), (46), and
(50) satisfy, on the probability-one event of distinct keys unequal to q,
C(q) ≤ D_1(L + k + 1) + ∑_{j=0}^{L−1} G_j + D_err + ∑_{i=1}^{k−1} W_i, D_1 = 7000. (54) The moment bounds in
Table 2 hold at the common parameter θ, almost surely for the conditional bounds. The growing and
future-block sums are independent conditional on P_L."

**Formalization Note.** (54) is stated for every input vector with distinct values none equal to `q`
(the probability-one event); `C(q)` is that of EmpiricalSort's output on the stream `X`. Table 2 at
`θ = 1/29360128` (53): `E[e^{θ∑G_j} | P_L] ≤ M_g^L` a.s., `E[e^{θ D_err}] ≤ M_b` with `M_b` of (52),
`E[e^{θ∑W_i} | P_L] ≤ M_s^{k−1}` a.s. with `M_s = 1 + 2e^{−1/3}/(1 − e^{−1/6})` (p.35); conditioning
is on `σ(P_L)` (`HL n`, a sub-σ-algebra), integrands integrable. Conditional independence is
Mathlib's `CondIndepFun` given `σ(P_L)`. -/
theorem lemma_4_14 :
    (∀ n, 16 * T ≤ n → ∀ q : ℝ, 0 < q → q < 1 → ∀ X : Fin n → ℝ, Function.Injective X →
      (∀ a, X a ≠ q) →
        (valueCrossings empiricalSort X 1 1 q : ℝ) ≤
          7000 * ((L n : ℝ) + k n + 1) + GSum n (iidLt X) (fun a => decide (q < vecVal X a)) +
            Derr (prefixOf X) q + WSum X q) ∧
    (∀ n, 16 * T ≤ n → ∀ q : ℝ, 0 < q → q < 1 →
      HL n ≤ MeasurableSpace.pi ∧
      Integrable (fun X : Fin n → ℝ =>
          Real.exp (1 / 29360128 * GSum n (iidLt X) (fun a => decide (q < vecVal X a)))) (iidUnif n) ∧
      (iidUnif n)[fun X : Fin n → ℝ =>
          Real.exp (1 / 29360128 * GSum n (iidLt X) (fun a => decide (q < vecVal X a))) | HL n]
        ≤ᵐ[iidUnif n] (fun _ => Mg ^ L n) ∧
      Integrable (fun X : Fin n → ℝ => Real.exp (1 / 29360128 * Derr (prefixOf X) q)) (iidUnif n) ∧
      ∫ X, Real.exp (1 / 29360128 * Derr (prefixOf X) q) ∂(iidUnif n) ≤ Mb ∧
      Integrable (fun X : Fin n → ℝ => Real.exp (1 / 29360128 * WSum X q)) (iidUnif n) ∧
      (iidUnif n)[fun X : Fin n → ℝ => Real.exp (1 / 29360128 * WSum X q) | HL n]
        ≤ᵐ[iidUnif n] (fun _ => Ms ^ (k n - 1))) ∧
    ∀ n, 16 * T ≤ n → ∀ q : ℝ, 0 < q → q < 1 →
      ∃ hle : HL n ≤ MeasurableSpace.pi,
        ProbabilityTheory.CondIndepFun (HL n) hle
          (fun X : Fin n → ℝ => GSum n (iidLt X) (fun a => decide (q < vecVal X a)))
          (fun X : Fin n → ℝ => WSum X q) (iidUnif n) := by sorry

end RandOrderSort
