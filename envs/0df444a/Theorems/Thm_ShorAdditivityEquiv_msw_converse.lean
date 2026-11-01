-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_msw_converse
-- name    : ShorAdditivityEquiv.msw_converse
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:28.863646+00:00
-- url     : https://prove2.me/theorems/127c9bf5-e89b-4595-bca5-c8964a27d5da
-- title:
--   §3, p. 6 — every bipartite state is $V\rho V^\dagger$ for a full-rank $\rho$ on a space of dimension $\mathrm{rank}\,\sigma$
-- statement:
--   Let $\sigma$ be a density matrix on $\mathcal H_A\otimes\mathcal H_B$ and $r=\mathrm{rank}\,\sigma$. Then there are an isometry $V:\mathbb C^r\to\mathcal H_A\otimes\mathcal H_B$ ($V^\dagger V=I$) and a density matrix $\rho$ on $\mathbb C^r$ of full rank (positive definite, trace one) such that
--   $$
--   V\rho V^\dagger = \sigma .
--   $$
--   With $N(\mu)=\mathrm{Tr}_B(V\mu V^\dagger)$ this realizes every bipartite state in the Matsumoto–Shimono–Winter correspondence, with a full-rank input state; this is how the paper reduces statements about $E_F$ to statements about constrained capacities at full-rank inputs.
--
--   Differences from the source:
--   - encoding: an input space H_in with dim H_in = rank σ and a unitary embedding U : H_in → H_A ⊗ H_B → the index type Fin σ.rank and an isometry V : Matrix (A × B) (Fin σ.rank) ℂ with Vᴴ * V = 1; reason: same objects in coordinates
--   - encoding: a density matrix ρ ∈ H_in that has full rank → ρ.PosDef ∧ ρ.trace = 1; reason: a full-rank positive semidefinite matrix is positive definite
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §3, p. 6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information

open QAlgorithms
open scoped ComplexOrder Matrix

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §3, p.6, unnumbered: "Conversely, if we are given a bipartite state σ ∈ HA ⊗ HB, we can
find an input space Hin with dim Hin = rank σ, a density matrix ρ ∈ Hin, and a unitary embedding
U : Hin → Hout such that U(ρ) = σ. [...] Note that since we chose dim Hin = rank σ = rank ρ, ρ
has full rank in Hin."

**Formalization Note.** `H_in` is `ℂ^{rank σ}`, indexed by `Fin σ.rank`. The unitary embedding
`U(ρ) = VρV†` into `H_A ⊗ H_B` (the space `H_out` of the sentence, as the previous paragraph
says) is a matrix `V : (A × B) × Fin (rank σ)` with `V†V = 1`. "ρ is a density matrix of full
rank" is `ρ.PosDef ∧ ρ.trace = 1`. The channel `N(µ) = Tr_B U(µ)` of the next sentence is then a
definition, not a claim, and is not restated. -/
theorem msw_converse {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : Matrix (A × B) (A × B) ℂ) (hσ : IsDensityMatrix σ) :
    ∃ (V : Matrix (A × B) (Fin σ.rank) ℂ) (ρ : Matrix (Fin σ.rank) (Fin σ.rank) ℂ),
      Vᴴ * V = 1 ∧ ρ.PosDef ∧ ρ.trace = 1 ∧ V * ρ * Vᴴ = σ := by sorry

end ShorAdditivityEquiv
