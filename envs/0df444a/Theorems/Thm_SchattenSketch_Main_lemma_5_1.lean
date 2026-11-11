-- Prove2me | Theorems.Thm_SchattenSketch_Main_lemma_5_1
-- name    : SchattenSketch.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:45.826815+00:00
-- url     : https://prove2.me/theorems/0cb1b6b4-6922-4ba1-842a-8e18b45974a1
-- title:
--   Lemma 5.1 — multiscale head–tail dichotomy: some cutoff $h_j=\min\{jR,n\}$ has $T_{h_j}(A)\le\eta\|A\|_{S_1}$ or a residual of stable rank $\ge R/4$
-- statement:
--   Fix integers $1\le R\le n$ and $0<\eta<1$, and let
--   $$h_j=\min\{jR,n\},\qquad 0\le j\le J=\Bigl\lceil\log_2\frac{\sqrt{n/R}}\eta\Bigr\rceil .$$
--   For every real $n\times n$ matrix $A$ there is an inspected cutoff $h_j$ such that either $T_{h_j}(A)\le\eta\|A\|_{S_1}$, or the exact residual $A-A_{h_j}$ (with $A_h$ a best rank-$h$ approximation) has stable rank $\|A-A_{h_j}\|_F^2/\|A-A_{h_j}\|_{op}^2$ at least $R/4$.
--
--   This is the first step of the upper bound: among the few prepared cutoffs one either has a negligible tail or a well-spread tail whose nuclear norm can be estimated from spectral moments.
--
--   **Formalization Note.** The residual $A-A_h$ has singular values $\sigma_{h+1}(A)\ge\sigma_{h+2}(A)\ge\cdots$, so it is nonzero exactly when $a_h=\sigma_{h+1}(A)>0$, and then its stable rank is $F_h(A)^2/a_h^2$. The second alternative is stated in that form, with `tailFrobSq` and `tailTop`. $J$ is the natural-number ceiling of `Real.logb 2`.
--
--   Differences from the source:
--   - encoding: A − A_{h_j} has stable rank at least R/4 → 0 < a_{h_j} and R/4 ≤ F_{h_j}(A)²/a_{h_j}²; reason: A − A_h has singular values σ_{h+1}(A), σ_{h+2}(A), … (p. 12), so it is nonzero iff a_h > 0 and sr(A − A_h) = F_h²/a_h²; stable rank is defined for nonzero matrices
--   - encoding: J = ⌈log_2(√(n/R)/η)⌉ → ⌈Real.logb 2 (√(n/R)/η)⌉₊ (Nat.ceil); reason: the argument exceeds 1, so the ceiling is a positive integer
--   - encoding: singular values σ_1 ≥ … ≥ σ_n of A, ‖A‖_{S₁} = Σ σ_i(A) → published singVal (0-based: σ_i = singVal (i - 1)) and nucNorm = Σ_{j<n} singVal j A; reason: Lean indexing; same quantities
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 24, Lemma 5.1, (5.1)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_SchattenSketch_Main_Spectral

open WainwrightHDS.NucNorm

namespace SchattenSketch.Main

/-- Lemma 5.1 (multiscale head–tail dichotomy; Yang, p. 24). Fix `1 ≤ R ≤ n` and `0 < η < 1`, and
let `h_j = min{jR, n}` for `0 ≤ j ≤ J = ⌈log₂(√(n/R)/η)⌉`. For every real `n × n` matrix `A`,
some inspected cutoff `h_j` has either `T_{h_j}(A) ≤ η ‖A‖_{S₁}` or an exact residual
`A - A_{h_j}` of stable rank at least `R/4`. The residual is nonzero exactly when
`a_{h_j} = σ_{h_j + 1}(A) > 0`, and then its stable rank is `F_{h_j}(A)² / a_{h_j}²`, since its
singular values are `σ_{h_j+1}(A) ≥ σ_{h_j+2}(A) ≥ ⋯`. -/
theorem lemma_5_1 (n R : ℕ) (η : ℝ) (hR : 1 ≤ R) (hRn : R ≤ n) (hη : 0 < η) (hη1 : η < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ j : ℕ, j ≤ ⌈Real.logb 2 (Real.sqrt ((n : ℝ) / R) / η)⌉₊ ∧
      (tailNuc (min (j * R) n) A ≤ η * nucNorm A ∨
        (0 < tailTop (min (j * R) n) A ∧
          (R : ℝ) / 4 ≤ tailFrobSq (min (j * R) n) A / tailTop (min (j * R) n) A ^ 2)) := by sorry

end SchattenSketch.Main
