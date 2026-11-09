-- Prove2me | Theorems.Thm_SelectiveDPT_remark_2_13
-- name    : SelectiveDPT.remark_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:46.796081+00:00
-- url     : https://prove2.me/theorems/9fd37bf8-65e9-4ea6-a107-e9a09286ba3f
-- title:
--   Remark 2.13 — the two forms of the progress rate $c(\Gamma)$ agree
-- statement:
--   Let $D \subseteq X^\iota$ be a nonempty domain over a nonempty index set $\iota$ and let $\Gamma$ be a positive-definite $|D|\times|D|$ matrix. Then the progress rate
--   $$c(\Gamma) = \max_{i,p} \big\|O_{i,p}^\dagger\Gamma^{1/2}O_{i,p}\Gamma^{-1/2}\big\|^2$$
--   is the greatest value of
--   $$\frac{\mathrm{Tr}[\Gamma\, O_{i,p}^\dagger\, \rho\, O_{i,p}]}{\mathrm{Tr}[\Gamma\rho]}$$
--   over all indices $i$, phases $p \in \mathbb Z_d$ and density matrices $\rho$ on $\mathbb C^D$. In particular the two expressions for $c$ in Propositions 2.12 and 2.14 coincide.
--
--   Theorem 3.1 bounds the progress through the ratio form; Theorem 4.7 computes the rate of a tensor power through the norm form.
--
--   **Formalization Note** The traces are real for Hermitian $\Gamma$ and density $\rho$ and are taken as real parts.
--
--   Differences from the source:
--   - generalization: Γ positive definite with smallest eigenvalue 1 and Γ|D⟩ = |D⟩ (the matrices of Proposition 2.12) → any positive-definite Γ; reason: the chain of equalities uses only that Γ is positive definite; the paper's matrices are positive definite
--   - encoding: max_{i,p,ρ} of the ratio → IsGreatest of the set of ratios, with ι and D nonempty; reason: a maximum over an empty set is undefined; the paper's n ≥ 1 and D carries a distribution
--   - encoding: Tr[·] → real part of the trace; reason: the traces are real for Hermitian Γ and density ρ
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Remark 2.13, pp.16–17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_SelectiveDPT_rate

open scoped ComplexOrder

namespace SelectiveDPT

open QAlgorithms

/-- Remark 2.13 of Beame–Kornerup–Whitmeyer, *Strong Selective and List-Decoding Direct Product
Theorems for Quantum Query Complexity*, arXiv:2609.26678, pp.16–17: the two expressions of the
per-query progress rate in Propositions 2.12 and 2.14 agree,
`max_{i,p} ‖O_{i,p}† Γ^{1/2} O_{i,p} Γ^{−1/2}‖² = max_{i,p,ρ} Tr[Γ O_{i,p}† ρ O_{i,p}] / Tr[Γρ]`,
the maximum on the right over query indices `i`, phases `p` and density matrices `ρ` on `ℂ^D`.
Stated as: `rate D Γ` is the greatest element of the set of ratios.

**Formalization Note.** `Γ` is positive definite (the remark concerns the matrices of
Proposition 2.12, positive definite with smallest eigenvalue `1`; only positive definiteness is
used). The traces are real for Hermitian `Γ` and density `ρ` and are taken as real parts. A
maximum over an empty set does not exist, so the index type and `D` are nonempty. -/
theorem remark_2_13 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (hD : D.Nonempty) (Γ : Matrix D D ℂ) (hΓ : Γ.PosDef) :
    IsGreatest {r : ℝ | ∃ (q : ι × ZMod d) (ρ : Matrix D D ℂ), IsDensityMatrix ρ ∧
        r = (Γ * (oracleOn D q.1 q.2).conjTranspose * ρ * oracleOn D q.1 q.2).trace.re /
          (Γ * ρ).trace.re}
      (rate D Γ) := by sorry

end SelectiveDPT
