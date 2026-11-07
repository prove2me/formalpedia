-- Prove2me | Theorems.Thm_QMAPlusGap_theorem_A_4
-- name    : QMAPlusGap.theorem_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:20.793184+00:00
-- url     : https://prove2.me/theorems/d535d396-b15b-4a8b-89c1-2722c5cf1cfc
-- title:
--   Theorem A.4 [JWX26, Thm 1.3] — trace-norm de Finetti $8\ell\sqrt{d-1}/a$
-- statement:
--   **Theorem A.4 (Jeronimo–Wu–Xu).** Let $2\le\ell\le a$, let $\Omega_a$ be a density operator supported on $\mathrm{Sym}^a(\mathcal H)$ with $d=\dim\mathcal H$, and let $\Omega_\ell$ be its reduced state on $\ell$ registers. Then there is a probability measure $\nu$ on the unit sphere of $\mathcal H$ such that
--   $$
--   \Big\|\Omega_\ell-\int(|\psi\rangle\langle\psi|)^{\otimes\ell}\,d\nu(\psi)\Big\|_1\ \le\ \frac{8\ell\sqrt{d-1}}{a}.
--   $$
--
--   This optimal-rate trace-norm de Finetti theorem is applied, in Lemma 14, on the high-eigenvalue subspace of rank at most $m$.
--
--   Differences from the source:
--   - encoding: a probability measure ν on the unit sphere of H; d = dim H → a probability measure on ℂ^ι concentrated on the unit sphere; d = Fintype.card ι; reason: same objects
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Theorem A.4, p.36 (cited from Jeronimo, Wu, Xu [JWX26, Theorem 1.3])

import Mathlib
import Definitions.Def_QMAPlusGap_IsSymSupported
import Definitions.Def_QMAPlusGap_reduce
import Definitions.Def_QMAPlusGap_IsSphereProb
import Definitions.Def_QMAPlusGap_tpMixture
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Theorem A.4 (Jeronimo–Wu–Xu [JWX26, Theorem 1.3])**, cited in Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), p.36: "Let 2 ≤ ℓ ≤ a, and let Ω_a be a
density operator supported on Sym^a(H), where d = dim H. If Ω_ℓ is its reduced state on ℓ registers, then there is
a probability measure ν on the unit sphere of H such that ∥Ω_ℓ − ∫ (|ψ⟩⟨ψ|)^{⊗ℓ} dν(ψ)∥₁ ≤ 8ℓ√(d − 1)/a."

**Formalization Note** `H = ℂ^ι`, `d = Fintype.card ι` (`d ≥ 1` whenever a density operator exists); posed as this
paper quotes it, without the `d ≥ 2` of [JWX26] (at `d = 1` both sides are `0`). `∥·∥₁` is
`WildeQIT.traceNorm`. -/
theorem theorem_A_4 {ι : Type} [Fintype ι] [DecidableEq ι] (a ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (hℓa : ℓ ≤ a)
    (Ω : Matrix (Fin a → ι) (Fin a → ι) ℂ) (hΩ : WildeQIT.IsDensityOperator Ω) (hΩs : IsSymSupported Ω) :
    ∃ ν : Measure (ι → ℂ), IsSphereProb ν ∧
      WildeQIT.traceNorm (reduce ℓ Ω - tpMixture ℓ ν) ≤
        8 * (ℓ : ℝ) * Real.sqrt ((Fintype.card ι : ℝ) - 1) / (a : ℝ) := by sorry

end QMAPlusGap
