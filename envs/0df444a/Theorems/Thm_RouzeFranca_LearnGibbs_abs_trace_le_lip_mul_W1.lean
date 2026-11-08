-- Prove2me | Theorems.Thm_RouzeFranca_LearnGibbs_abs_trace_le_lip_mul_W1
-- name    : RouzeFranca.LearnGibbs.abs_trace_le_lip_mul_W1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:47:59.123955+00:00
-- url     : https://prove2.me/theorems/b46ef98b-350f-47b9-9bfc-80df2cda5dca
-- title:
--   Eq. (40) — $|\operatorname{tr}[X(\rho-\sigma)]|\le\|X\|_{\mathrm{Lip}}\,W_1(\rho,\sigma)$
-- statement:
--   Let $\|\cdot\|_{\mathrm{Lip}}$ be a Lipschitz constant on observables (nonnegative and absolutely homogeneous) and $W_1$ the induced Wasserstein distance. Let $\rho,\sigma$ be operators and $w$ a real number with $W_1(\rho,\sigma)\le w$. Then for every Hermitian observable $X$,
--   $$
--   \bigl|\operatorname{tr}[X(\rho-\sigma)]\bigr|\ \le\ \|X\|_{\mathrm{Lip}}\cdot w .
--   $$
--   In particular $|\operatorname{tr}[X(\rho-\sigma)]|\le\|X\|_{\mathrm{Lip}}\,W_1(\rho,\sigma)$.
--
--   This duality converts a Wasserstein bound, obtained from the transportation cost inequality, into a bound on the expectation value of every observable; it is the last step of the proof of the main theorem.
--
--   **Formalization Note** The case $\|X\|_{\mathrm{Lip}}=0$ is included.
--
--   Differences from the source:
--   - generalization: the differential Lipschitz constant ∥·∥_Lip,∇ and W_1,∇, ρ, σ states → every nonnegative absolutely homogeneous lip (IsLipSeminorm), ρ, σ any matrices; reason: the proof uses only these two properties; ∥·∥_Lip,∇ has them, so the source's statement is a special case
--   - encoding: W_1,∇(ρ, σ) as a supremum → a bound w with W1Le lip ρ σ w; take w = W_1(ρ, σ); reason: avoids a real supremum; same instances
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, §B.1.2, Eq. (40), p. 23

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs
import Definitions.Def_RouzeFranca_LearnGibbs_W1Le
import Definitions.Def_RouzeFranca_LearnGibbs_IsLipSeminorm

open Matrix

namespace RouzeFranca.LearnGibbs

/-- **Eq. (40) (duality between Lipschitz constant and Wasserstein distance).** Let `lip` be a
Lipschitz constant (nonnegative and absolutely homogeneous). If `W₁(ρ, σ) ≤ w` for the
Wasserstein distance induced by `lip`, then for every observable `X`,
`|tr[X(ρ − σ)]| ≤ ‖X‖_Lip · w`; that is, `|tr[X(ρ − σ)]| ≤ ‖X‖_Lip W₁(ρ, σ)`.

Rouzé, Stilck França, arXiv:2107.03333v4, §B.1.2, Eq. (40), p. 23: "W1,∇(ρ, σ) :=
sup_{X=X†, ∥X∥Lip,∇≤1} |Tr(X(ρ − σ))|. It immediately follows from the definitions that for any
observable X: |tr[X(ρ − σ)]| ≤ ∥X∥Lip,∇ W1,∇(ρ, σ). (40)"

**Formalization Note.** Stated for every Lipschitz constant satisfying `IsLipSeminorm` (in
particular `‖·‖_Lip,∇` of (38) and `‖·‖_Lip,□` of (34)) and for arbitrary matrices `ρ, σ`.
`W₁(ρ, σ) ≤ w` is `W1Le lip ρ σ w`; taking `w = W₁(ρ, σ)` gives (40). The case `‖X‖_Lip = 0` is
included. -/
theorem abs_trace_le_lip_mul_W1 {n : ℕ} (lip : Mat n → ℝ) (hlip : IsLipSeminorm lip)
    (ρ σ : Mat n) (w : ℝ) (hW : W1Le lip ρ σ w) (X : Mat n) (hX : X.IsHermitian) :
    |(trace (X * (ρ - σ))).re| ≤ lip X * w := by sorry

end RouzeFranca.LearnGibbs
