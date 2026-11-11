-- Prove2me | Theorems.Thm_SchattenSketch_Main_theorem_5_2
-- name    : SchattenSketch.Main.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:39.121467+00:00
-- url     : https://prove2.me/theorems/1dd42902-08a3-41ca-88ef-d7215c864395
-- title:
--   Theorem 5.2 — effective-rank Gaussian covariance bound [KL17], with uniform absolute constants (reading of a typo)
-- statement:
--   There are absolute constants $C_{cov,1},C_{cov,2}>0$ with the following property. Let $s\ge 1$ and let $G\in\mathbb R^{s\times n}$ have independent $N(0,1/s)$ entries. For every deterministic $D\in\mathbb R^{n\times r}$ and $0<\delta<1/2$, with probability at least $1-\delta$,
--   $$\bigl\|D^\top(G^\top G-I)D\bigr\|_{op}\le C_{cov,1}\Bigl(\frac{\|D\|_{op}\|D\|_F}{\sqrt s}+\frac{\|D\|_F^2}s\Bigr)+C_{cov,1}\|D\|_{op}^2\Bigl(\sqrt{\frac{\log(1/\delta)}s}+\frac{\log(1/\delta)}s\Bigr).$$
--   In particular, if $0<\alpha<1$, $\|D\|_{op}\le 1$ and $s\ge C_{cov,2}\,\alpha^{-2}(\|D\|_F^2+\log(1/\delta))$, the right side is at most $\alpha$.
--
--   The theorem gives the simultaneous covariance event (5.5) for one Gaussian row sketch at every candidate cutoff, which is why the constants must not depend on $D$.
--
--   **Formalization Note.** $G=s^{-1/2}g$ with $g$ distributed as the published `gaussianMatrix s n`. $\|\cdot\|_{op}=\sigma_1$ and $\|\cdot\|_F=(\sum\sigma_i^2)^{1/2}$ are computed from singular values (`opNorm`, `frobNorm`), as on p. 4.
--
--   Differences from the source:
--   - reading: for every D and 0 < δ < 1/2 there are fixed absolute constants C_cov,1, C_cov,2 > 0 → ∃ C₁ C₂ > 0 first, then ∀ s n r D δ; reason: obvious typo (INSIGHTS I1): the printed order makes both clauses trivial; (5.7) uses the constants uniformly in D
--   - reading: α unquantified in the 'in particular' clause → ∀ α with 0 < α < 1; reason: INSIGHTS I1: the clause fails for large α; the paper uses it with 0 < α < 1/10
--   - encoding: G ∈ R^{s×n} with independent N(0, 1/s) entries → G = s^{-1/2} g, g ∼ gaussianMatrix s n, with s ≥ 1; reason: the same law; N(0, 1/s) needs s ≥ 1
--   - encoding: ‖·‖_op, ‖·‖_F → opNorm = singVal 0, frobNorm = √(Σ singVal²); reason: the paper's definitions on p. 4
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 25, Theorem 5.2, (5.3)

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SchattenSketch_Main_Spectral

open MeasureTheory GaussianMatrix

namespace SchattenSketch.Main

/-- Theorem 5.2 (effective-rank Gaussian covariance bound [KL17]; Yang, p. 25), with the absolute
constants quantified first. There are absolute constants `C_cov,1, C_cov,2 > 0` such that: let
`G = s^{-1/2} g ∈ ℝ^{s×n}` with `g` a standard Gaussian matrix (so `G` has independent
`N(0, 1/s)` entries). For every deterministic `D ∈ ℝ^{n×r}` and `0 < δ < 1/2`, with probability at
least `1 - δ`,
`‖Dᵀ(GᵀG - I)D‖_op ≤ C_cov,1 (‖D‖_op ‖D‖_F/√s + ‖D‖_F²/s)
  + C_cov,1 ‖D‖_op² (√(log(1/δ)/s) + log(1/δ)/s)`;
and if `0 < α < 1`, `‖D‖_op ≤ 1` and `s ≥ C_cov,2 α⁻² (‖D‖_F² + log(1/δ))`, the right side is at
most `α`. -/
theorem theorem_5_2 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (s n r : ℕ), 1 ≤ s → ∀ (D : Matrix (Fin n) (Fin r) ℝ) (δ : ℝ), 0 < δ → δ < 1 / 2 →
        let rhs : ℝ :=
          C₁ * (opNorm D * frobNorm D / Real.sqrt s + frobNorm D ^ 2 / s) +
            C₁ * opNorm D ^ 2 * (Real.sqrt (Real.log (1 / δ) / s) + Real.log (1 / δ) / s)
        ENNReal.ofReal (1 - δ) ≤
            gaussianMatrix s n {g |
              let G : Matrix (Fin s) (Fin n) ℝ := (1 / Real.sqrt s) • Matrix.of g
              opNorm (D.transpose * (G.transpose * G - 1) * D) ≤ rhs} ∧
          ∀ α : ℝ, 0 < α → α < 1 → opNorm D ≤ 1 →
            C₂ * α⁻¹ ^ 2 * (frobNorm D ^ 2 + Real.log (1 / δ)) ≤ s → rhs ≤ α := by sorry

end SchattenSketch.Main
