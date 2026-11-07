-- Prove2me | Theorems.Thm_QMAPlusGap_lemma_10
-- name    : QMAPlusGap.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:07:40.89541+00:00
-- url     : https://prove2.me/theorems/4a36ceeb-6975-4f58-bfec-194ed1066fbe
-- title:
--   Lemma 10 — Hilbert–Schmidt bound for $(B^{1/2})^{\otimes j}\rho(B^{1/2})^{\otimes j}$
-- statement:
--   Let $\mathcal H=\mathbb C^{\kappa}$ have its computational basis, and let $0\preceq B\preceq I$ satisfy
--   $$
--   \sup_{|\psi\rangle\ge0,\ \||\psi\rangle\|=1}\langle\psi|B|\psi\rangle\le r<1 .
--   $$
--   Let $j\ge1$, let $\rho\in\mathrm D(\mathcal H^{\otimes j})$ be entrywise nonnegative, and let $\mu$ be a probability measure on unit vectors such that $\sigma=\int(|\phi\rangle\langle\phi|)^{\otimes j}d\mu(\phi)$ satisfies $\|\rho-\sigma\|_2\le\varepsilon$. Then
--   $$
--   \big\|(B^{1/2})^{\otimes j}\rho(B^{1/2})^{\otimes j}\big\|_2^2\ \le\ \frac14+\Big(1-\frac{(1-\sqrt r)^2}{4}\Big)^{j}+\Big(\frac{1+\sqrt r}{2}\Big)^{2j}+4\varepsilon .\tag{6}
--   $$
--
--   This is the per-sector estimate inside the proof of Proposition 9: an entrywise nonnegative state close to a tensor-power mixture has Hilbert–Schmidt mass at most about $1/4$ after the test $B$ on every register.
--
--   Differences from the source:
--   - encoding: sup over |ψ⟩ ≥ 0, ∥|ψ⟩∥ = 1 of ⟨ψ|B|ψ⟩ ≤ r; B^{1/2}; μ a probability measure on unit vectors → the pointwise bound for every unit ψ ≥ 0; CFC.sqrt B; a probability measure on ℂ^κ concentrated on the unit sphere; reason: a supremum is ≤ r iff every term is; same objects
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 10, p.17

import Mathlib
import Definitions.Def_QMAPlusGap_IsNonnegVec
import Definitions.Def_QMAPlusGap_IsEntrywiseNonneg
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_QMAPlusGap_expect
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_QMAPlusGap_IsSphereProb
import Definitions.Def_QMAPlusGap_tpMixture
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_hsNorm

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Lemma 10**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), p.17: "Let 0 ⪯ B ⪯ I satisfy sup_{|ψ⟩≥0, ∥|ψ⟩∥=1} ⟨ψ|B|ψ⟩ ≤ r < 1. Let j ≥ 1, let
ρ ∈ D(H^{⊗j}) be entrywise nonnegative in the fixed computational basis, and let μ be a probability measure on unit
vectors such that σ = ∫ (|ϕ⟩⟨ϕ|)^{⊗j} dμ(ϕ) satisfies ∥ρ − σ∥₂ ≤ ε. Then
∥(B^{1/2})^{⊗j} ρ (B^{1/2})^{⊗j}∥₂² ≤ 1/4 + (1 − (1 − √r)²/4)^j + ((1 + √r)/2)^{2j} + 4ε. (6)"

**Formalization Note** `H = ℂ^κ`; the supremum hypothesis is stated pointwise for every unit `ψ ≥ 0`;
`B^{1/2} = CFC.sqrt B`; `∥·∥₂` is `WildeQIT.hsNorm`; `μ` is a probability measure concentrated on the unit
sphere. -/
theorem lemma_10 {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℂ) (hB0 : B.PosSemidef)
    (hB1 : (1 - B).PosSemidef) (r : ℝ)
    (hsup : ∀ ψ : κ → ℂ, IsNonnegVec ψ → ArgmaxDeFinetti.vnorm ψ = 1 → (expect B ψ).re ≤ r) (hr : r < 1)
    (j : ℕ) (hj : 1 ≤ j) (ρ : Matrix (Fin j → κ) (Fin j → κ) ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (hρnn : IsEntrywiseNonneg ρ) (μ : Measure (κ → ℂ)) (hμ : IsSphereProb μ) (ε : ℝ)
    (hε : WildeQIT.hsNorm (ρ - tpMixture j μ) ≤ ε) :
    WildeQIT.hsNorm (WildeQIT.Schumacher.tensorPow j (CFC.sqrt B) * ρ * WildeQIT.Schumacher.tensorPow j (CFC.sqrt B)) ^ 2 ≤
      1 / 4 + (1 - (1 - Real.sqrt r) ^ 2 / 4) ^ j + ((1 + Real.sqrt r) / 2) ^ (2 * j) + 4 * ε := by sorry

end QMAPlusGap
