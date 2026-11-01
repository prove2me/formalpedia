-- Prove2me | Theorems.Thm_WildeQIT_Schumacher_theorem_18_2_1_direct
-- name    : WildeQIT.Schumacher.theorem_18_2_1_direct
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:42.280135+00:00
-- url     : https://prove2.me/theorems/fd2a553a-cbc1-4a59-8f3c-cfdcdbbfefbe
-- title:
--   Theorem 18.2.1 (direct part): $H(A)_\rho$ is an achievable compression rate
-- statement:
--   Let $\rho_A$ be the density operator of a quantum information source on a finite-dimensional space, with quantum entropy $H(A)_\rho$ (bits). Then $H(A)_\rho$ is an achievable rate of quantum data compression: for every $\delta>0$ and $\varepsilon\in(0,1)$, for all sufficiently large $n$ there is an $(n, H(A)_\rho+\delta, \varepsilon)$ quantum compression code, i.e. channels $\mathcal E_{A^n\to W}$, $\mathcal D_{W\to\hat A^n}$ with $\dim\mathcal H_W\le 2^{n(H(A)_\rho+\delta)}$ and
--
--   $$
--   \frac12\left\|(\phi^\rho_{RA})^{\otimes n}-(\mathcal D\circ\mathcal E)\big((\phi^\rho_{RA})^{\otimes n}\big)\right\|_1\le\varepsilon .
--   $$
--
--   This is the direct coding theorem of Schumacher compression (§18.2.1).
--
--   **Formalization Note** $H(A)_\rho$ is the published `QAlgorithms.vnEntropy`. Codes and achievability are `IsCompressionCode` and `IsAchievableRate`.
--
--   Differences from the source:
--   - encoding: dim(H_W) = 2^{nR} → dim(H_W) ≤ 2^{nR}; reason: a dimension is an integer; a smaller W embeds isometrically into one of dimension ⌊2^{nR}⌋ with the same error, so the achievable rates are the same.
--   - encoding: purification (18.3) built from an ensemble of ρ → the canonical purification Σ_r |r⟩ ⊗ √ρ|r⟩, systems grouped RⁿAⁿ; reason: purifications differ by an isometry on the reference, which commutes with channels on Aⁿ and preserves the trace norm, so the error (18.5) is the same.
--   - encoding: channels → Choi–Kraus form (WildeQIT.QChannel); reason: Theorem 4.4.1, every channel has this form.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 18.2.1 and §18.2.1, p. 524

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Schumacher_IsAchievableRate

namespace WildeQIT.Schumacher

/-- **Theorem 18.2.1, direct coding theorem** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §18.2.1, p. 524): "Schumacher's compression protocol demonstrates that the
quantum entropy `H(A)_ρ` is an achievable rate for quantum data compression."

**Formalization Note.** `H(A)_ρ` is the published `QAlgorithms.vnEntropy` (bits); achievability
is `IsAchievableRate` (for every `δ > 0` and `ε ∈ (0, 1)`, an `(n, H(A)_ρ + δ, ε)` code exists
for all sufficiently large `n`, with error criterion (18.5)). -/
theorem theorem_18_2_1_direct {a : Type} [Fintype a] [DecidableEq a] (ρ : Matrix a a ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) :
    IsAchievableRate ρ (QAlgorithms.vnEntropy ρ) := by sorry

end WildeQIT.Schumacher
