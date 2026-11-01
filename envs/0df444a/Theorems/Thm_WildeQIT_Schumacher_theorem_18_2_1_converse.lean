-- Prove2me | Theorems.Thm_WildeQIT_Schumacher_theorem_18_2_1_converse
-- name    : WildeQIT.Schumacher.theorem_18_2_1_converse
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:51.167144+00:00
-- url     : https://prove2.me/theorems/52a0884f-5d67-458e-98b7-ee8acc7e2d4a
-- title:
--   Theorem 18.2.1 (converse part): every achievable rate satisfies $R \ge H(A)_\rho$
-- statement:
--   Let $\rho_A$ be the density operator of a quantum information source on a finite-dimensional space, with quantum entropy $H(A)_\rho$ (bits). If $R$ is an achievable rate of quantum data compression for $\rho$ (with the error criterion (18.5)), then
--
--   $$
--   R \ge H(A)_\rho .
--   $$
--
--   This is the converse theorem of Schumacher compression (§18.2.2): no sequence of protocols compressing below the quantum entropy has vanishing error.
--
--   **Formalization Note** $H(A)_{\phi^\rho} = H(A)_\rho$ since the marginal of $\phi^\rho_{RA}$ on $A$ is $\rho$; it is the published `QAlgorithms.vnEntropy`. Achievability is `IsAchievableRate`.
--
--   Differences from the source:
--   - encoding: dim(H_W) = 2^{nR} → dim(H_W) ≤ 2^{nR}; reason: a dimension is an integer; a smaller W embeds isometrically into one of dimension ⌊2^{nR}⌋ with the same error, so the achievable rates are the same.
--   - encoding: purification (18.3) built from an ensemble of ρ → the canonical purification Σ_r |r⟩ ⊗ √ρ|r⟩, systems grouped RⁿAⁿ; reason: purifications differ by an isometry on the reference, which commutes with channels on Aⁿ and preserves the trace norm, so the error (18.5) is the same.
--   - encoding: channels → Choi–Kraus form (WildeQIT.QChannel); reason: Theorem 4.4.1, every channel has this form.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 18.2.1 and §18.2.2, pp. 526–527 (conclusion after (18.30), p. 527)

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Schumacher_IsAchievableRate

namespace WildeQIT.Schumacher

/-- **Theorem 18.2.1, converse theorem** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §18.2.2, p. 527): "an achievable rate `R` of quantum data compression
necessarily satisfies `R ≥ H(A)_{ϕ^ρ}`."

**Formalization Note.** `H(A)_{ϕ^ρ} = H(A)_ρ` (the marginal of `ϕ^ρ_{RA}` on `A` is `ρ`) is the
published `QAlgorithms.vnEntropy ρ` (bits); achievability is `IsAchievableRate` with the error
criterion (18.5). -/
theorem theorem_18_2_1_converse {a : Type} [Fintype a] [DecidableEq a] (ρ : Matrix a a ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (R : ℝ) (hR : IsAchievableRate ρ R) :
    QAlgorithms.vnEntropy ρ ≤ R := by sorry

end WildeQIT.Schumacher
