-- Prove2me | Theorems.Thm_WildeQIT_Schumacher_theorem_18_2_1
-- name    : WildeQIT.Schumacher.theorem_18_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:39:36.858346+00:00
-- url     : https://prove2.me/theorems/bdbafe34-1915-4b99-9df8-0623565ca689
-- title:
--   Theorem 18.2.1 (Quantum Data Compression): the compression limit of $\rho$ equals $H(A)_\rho$
-- statement:
--   Let $\rho_A$ be the density operator of a quantum information source on a finite-dimensional space $\mathcal H_A$, and let $H(A)_\rho = -\mathrm{Tr}\{\rho\log\rho\}$ be its quantum entropy (bits). Call $R$ an achievable rate if for every $\delta>0$ and $\varepsilon\in(0,1)$ and all sufficiently large $n$ there are channels $\mathcal E_{A^n\to W}$, $\mathcal D_{W\to\hat A^n}$ with $\dim\mathcal H_W \le 2^{n(R+\delta)}$ and error (18.5) at most $\varepsilon$. Then the set of achievable rates is nonempty and bounded below, and the quantum data compression limit (its infimum) is the quantum entropy:
--
--   $$
--   \inf\{R : R \text{ achievable for } \rho\} = H(A)_\rho .
--   $$
--
--   Schumacher compression gives the quantum entropy its operational meaning as the number of qubits per source state needed to transmit a quantum information source faithfully.
--
--   **Formalization Note** $H(A)_\rho$ is the published `QAlgorithms.vnEntropy`. The limit is `compressionLimit`, a real `sInf`; the first two conjuncts make it a genuine infimum.
--
--   Differences from the source:
--   - encoding: dim(H_W) = 2^{nR} → dim(H_W) ≤ 2^{nR}; reason: a dimension is an integer; a smaller W embeds isometrically into one of dimension ⌊2^{nR}⌋ with the same error, so the achievable rates are the same.
--   - encoding: purification (18.3) built from an ensemble of ρ → the canonical purification Σ_r |r⟩ ⊗ √ρ|r⟩, systems grouped RⁿAⁿ; reason: purifications differ by an isometry on the reference, which commutes with channels on Aⁿ and preserves the trace norm, so the error (18.5) is the same.
--   - encoding: channels → Choi–Kraus form (WildeQIT.QChannel); reason: Theorem 4.4.1, every channel has this form.
--   - encoding: infimum of achievable rates → real sInf, with the set asserted nonempty and bounded below; reason: Lean's sInf is 0 on an empty or unbounded set; the book's infimum presupposes both.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 18.2.1, p. 524; definitions §18.1, p. 523

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Schumacher_compressionLimit

namespace WildeQIT.Schumacher

/-- **Theorem 18.2.1 (Quantum Data Compression)** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, p. 524): "Suppose that `ρ_A` is the density operator corresponding to
a quantum information source. Then the quantum entropy `H(A)_ρ` is equal to the quantum data
compression limit of `ρ`."

The first two conjuncts say that the set of achievable rates is nonempty and bounded below, so
that its infimum (the compression limit, §18.1, p. 523) is a genuine infimum; the third is the
book's identity.

**Formalization Note.** `ℋ_A` is finite-dimensional with standard basis indexed by the finite
type `a`; the quantum entropy `H(A)_ρ = −Tr{ρ log ρ}` (Definition 11.1.1) is the published
`QAlgorithms.vnEntropy`, in bits. Codes are `IsCompressionCode` (error criterion (18.5) on the
canonical purification, `dim(ℋ_W) ≤ 2^{nR}`); achievability is `IsAchievableRate`. -/
theorem theorem_18_2_1 {a : Type} [Fintype a] [DecidableEq a] (ρ : Matrix a a ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) :
    {R : ℝ | IsAchievableRate ρ R}.Nonempty ∧ BddBelow {R : ℝ | IsAchievableRate ρ R} ∧
      compressionLimit ρ = QAlgorithms.vnEntropy ρ := by sorry

end WildeQIT.Schumacher
