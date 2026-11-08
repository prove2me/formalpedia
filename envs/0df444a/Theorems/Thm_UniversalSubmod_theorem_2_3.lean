-- Prove2me | Theorems.Thm_UniversalSubmod_theorem_2_3
-- name    : UniversalSubmod.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:37.997083+00:00
-- url     : https://prove2.me/theorems/599c7269-4264-49f1-aa46-ac96ac0ade2e
-- title:
--   Theorem 2.3 — lower pairwise covariances give a larger semidefinite extension: $F(x,\Sigma)\ge F(x,\Sigma')$
-- statement:
--   Let $f:2^{[n]}\to\mathbb R_{\ge0}$ be nonnegative submodular and $F:[0,1]^n\times\mathcal E_n\to\mathbb R_{\ge0}$ its semidefinite extension, $F(x,\Sigma)=\mathbb E[f(\{i:G_i\ge\Phi^{-1}(1-x_i)\})]$ with $G\sim N(0,\Sigma)$. If $\Sigma,\Sigma'\in\mathcal E_n$ satisfy $\sigma_{ij}\le\sigma'_{ij}$ for all $i\ne j$, and $x\in[0,1]^n$, then
--   $$
--   F(x,\Sigma)\ \ge\ F(x,\Sigma').
--   $$
--
--   Lower pairwise covariances imply a higher submodular expectation. Applied to near-orthogonal vectors against the equicorrelated matrix $(1-\varepsilon)I+\varepsilon J$, it reduces Theorem 2.4 to independent sampling.
--
--   **Formalization Note** $\mathcal E_n$ is `CorrMatrix` (positive semidefinite, unit diagonal) and $F(x,\Sigma)$ is `semidefExt`, an expectation under Mathlib's `multivariateGaussian 0 Σ` with the threshold written $1-x_i\le\Phi(G_i)$.
--
--   Differences from the source:
--   - encoding: $R=\{i:G_i\ge\Phi^{-1}(1-x_i)\}$ with $G=(\langle v_i,Z\rangle)_i$, $Z\sim N(0,I_n)$ → $\{i: 1-x_i\le\Phi(G_i)\}$ with $G\sim$ `multivariateGaussian 0 Σ`; reason: $G$ has law $N(0,\Sigma)$; the events agree for $x_i\in(0,1)$, and at $x_i\in\{0,1\}$ this is the convention $\Phi^{-1}(1)=+\infty$, $\Phi^{-1}(0)=-\infty$ used by the proof on p.20
--   - encoding: $\Sigma\in\mathcal E_n$ → `CorrMatrix Σ`: `Σ.PosSemidef` and unit diagonal; reason: the definition of $\mathcal E_n$
--   - encoding: the ground set $[n]$, subsets $S\subseteq[n]$, $f:2^{[n]}\to\mathbb R_{\ge0}$ → `Fin n`, `Finset (Fin n)`, a real-valued `f` with $f(S)\ge0$ for all $S$; reason: a relabelling of $[n]$; the same functions
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), Theorem 2.3, p.7 (proof p.20)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_UniversalSubmod_CorrMatrix
import Definitions.Def_UniversalSubmod_semidefExt

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

/-- **Theorem 2.3** (Gaussian comparison for submodular functions; Adamczyk, Ueltzen, Vondrák,
*Optimal universal sets for submodular functions*, manuscript of November 3, 2026, Theorem 2.3,
p.7; proof p.20). Let `f : 2^[n] → ℝ≥0` be nonnegative submodular and `F : [0,1]^n × E_n → ℝ≥0`
its semidefinite extension. If `Σ, Σ' ∈ E_n` satisfy `σᵢⱼ ≤ σ'ᵢⱼ` for all `i ≠ j`, and
`x ∈ [0,1]^n`, then `F(x, Σ) ≥ F(x, Σ')`.

**Formalization Note.** `E_n` is `CorrMatrix` (PSD, unit diagonal) and `F(x, Σ)` is `semidefExt`
(expectation under `multivariateGaussian 0 Σ` with the `Φ`-side threshold; see that definition). -/
theorem theorem_2_3 {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (S S' : Matrix (Fin n) (Fin n) ℝ) (hS : CorrMatrix S) (hS' : CorrMatrix S')
    (hle : ∀ i j, i ≠ j → S i j ≤ S' i j)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    semidefExt f x S' ≤ semidefExt f x S := by sorry

end UniversalSubmod
