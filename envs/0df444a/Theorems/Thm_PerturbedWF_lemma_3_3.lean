-- Prove2me | Theorems.Thm_PerturbedWF_lemma_3_3
-- name    : PerturbedWF.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:47:20.798202+00:00
-- url     : https://prove2.me/theorems/a20121f1-5529-4fab-8a37-1316a1a3b158
-- title:
--   Lemma 3.3: $\sum_{t=1}^T\|\mathbb E[\nabla g_t(q)]\|_1\le m\,\mathrm{OPT}$ for $q$ uniform on $[-1,1]^m$
-- statement:
--   For $t=1,\dots,T$ let $g_t:[-1,1]^m\to\mathbb R_{\ge0}$ be Lipschitz continuous, and suppose that for some fixed $a\in\mathbb R^m$ and every $q\in[-1,1]^m$
--   $$\sum_{t=1}^Tg_t(q)\le\mathrm{OPT}+\langle a,q\rangle.$$
--   Then, with $q$ uniform on $[-1,1]^m$,
--   $$\sum_{t=1}^T\big\|\mathbb E[\nabla g_t(q)]\big\|_1\le m\,\mathrm{OPT}.$$
--
--   Applied to $g_t=H_{t-1}-H_t$ with $H_t(q)=W_t^*(Aq)$, this bounds the expected movement by $m\cdot\mathrm{OPT}$ up to the factor $1/c_\tau$.
--
--   **Formalization Note.** OPT is any real number $B$. The partial derivatives are `fderiv ℝ (g t) q (e_i)`; they exist almost everywhere on the cube by Rademacher's theorem and depend only on the values of $g_t$ on the cube. $\|\cdot\|_1=\sum_i|\cdot|$ and $\mathbb E$ is the integral under the uniform law on the cube. The hypotheses hold on the closed cube, faces included.
--
--   Differences from the source:
--   - generalization: OPT, the optimal offline cost → any real number B; reason: the lemma uses no property of OPT, so the statement specializes to B = OPT
--   - encoding: g_t : [−1, 1]^m → ℝ≥0 Lipschitz; ∇g_t(q); ‖·‖₁ → g t : ℝ^m → ℝ, Lipschitz and nonnegative on the closed cube; ∇g_t(q) by its coordinates fderiv ℝ (g t) q (e_i); ‖·‖₁ = Σ_i |·|; E is the integral under cubeLaw m; reason: values off the cube are never used: the boundary of the cube is null and derivatives at interior points depend only on values in the cube
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Lemma 3.3, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_PerturbedWF_Algorithm

namespace PerturbedWF

open MeasureTheory

/-- **Lemma 3.3** (p.9, PDF p.10). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

For every `t ∈ [T]` let `g_t : [−1, 1]^m → ℝ_{≥0}` be Lipschitz continuous and satisfy
`∑_{t=1}^T g_t(q) ≤ OPT + ⟨a, q⟩` for some fixed vector `a ∈ ℝ^m` and every `q ∈ [−1, 1]^m`.
Then `∑_{t=1}^T ‖E[∇g_t(q)]‖₁ ≤ m · OPT`, the expectation over `q` uniform on `[−1, 1]^m`.

**Formalization Note.** `OPT` is any real number `B` (the lemma uses no other property of it).
`g t : ℝ^m → ℝ` is Lipschitz on the closed cube and nonnegative there, for `1 ≤ t ≤ T`; the bound
on `∑ g_t` holds on the closed cube, faces included. `∇g_t(q)` has the coordinates
`fderiv ℝ (g t) q (e_i)`; these exist almost everywhere on the cube (Rademacher) and depend only
on the values of `g t` on the cube. `‖·‖₁` is `∑_i |·|`, and `E` is the integral under the
uniform law `cubeLaw m`. -/
theorem lemma_3_3 (m N : ℕ) (g : ℕ → (Fin m → ℝ) → ℝ) (B : ℝ) (a : Fin m → ℝ)
    (hLip : ∀ t ∈ Finset.Icc 1 N, ∃ K, LipschitzOnWith K (g t) (Set.Icc (-1) 1))
    (hnonneg : ∀ t ∈ Finset.Icc 1 N, ∀ q ∈ Set.Icc (-1 : Fin m → ℝ) 1, 0 ≤ g t q)
    (hsum : ∀ q ∈ Set.Icc (-1 : Fin m → ℝ) 1,
      ∑ t ∈ Finset.Icc 1 N, g t q ≤ B + ∑ k, a k * q k) :
    ∑ t ∈ Finset.Icc 1 N, ∑ i : Fin m,
        |∫ q, fderiv ℝ (g t) q (Pi.single i (1 : ℝ)) ∂(cubeLaw m)| ≤ m * B := by sorry

end PerturbedWF
