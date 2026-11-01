-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_strongSuperadditive_of_pure
-- name    : ShorAdditivityEquiv.strongSuperadditive_of_pure
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:15.751745+00:00
-- url     : https://prove2.me/theorems/60136d3f-16d0-4ef9-b860-8d90a74506c0
-- title:
--   §6, p. 12 — it suffices to prove strong superadditivity for pure states
-- statement:
--   Fix finite-dimensional spaces $\mathcal H_{A_1},\mathcal H_{A_2},\mathcal H_{B_1},\mathcal H_{B_2}$. Suppose that every pure state $|\phi\rangle\langle\phi|$ ($\|\phi\|=1$) of the four-party system satisfies
--   $$
--   E_F\big(|\phi\rangle\langle\phi|\big) \ge E_F\big(\mathrm{Tr}_2|\phi\rangle\langle\phi|\big) + E_F\big(\mathrm{Tr}_1|\phi\rangle\langle\phi|\big).
--   $$
--   Then every density matrix $\sigma$ of the same system satisfies $E_F(\sigma)\ge E_F(\mathrm{Tr}_2\sigma)+E_F(\mathrm{Tr}_1\sigma)$. Here $E_F$ is taken across $A_1A_2\,|\,B_1B_2$ for the four-party states and across $A_i\,|\,B_i$ for the marginals.
--
--   This is the first reduction in the proof that additivity of $E_F$ implies its strong superadditivity.
--
--   Differences from the source:
--   - reading: "it is sufficient to prove this when σ is a pure state" → for fixed four spaces, the inequality for all pure states implies it for all density matrices of the same spaces; reason: the argument applies the pure-state inequality to the members |φi⟩ of a decomposition of σ, which live on the same space
--   - encoding: vectors |φ⟩, |v_i⟩ of the input space → unit vectors (‖φ‖ = 1); reason: |φ⟩⟨φ| is meant as a state (p.4: "the minimization ranges over states |φ⟩"); ensemble members are states
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §6, p. 12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_ShorAdditivityEquiv_trTwo
import Definitions.Def_ShorAdditivityEquiv_trOne

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §6, p.12, unnumbered: "First, we show that it is sufficient to prove this when σ is a
pure state. Consider the optimal decomposition of σ = Σi πi|φi⟩⟨φi|. We can apply the theorem
of strong subadditivity to the pure states |φi⟩⟨φi| [...]. Summing these inequalities over i
gives the desired inequality."

For a fixed quadripartite system `H_{A1} ⊗ H_{A2} ⊗ H_{B1} ⊗ H_{B2}`: if the strong
superadditivity inequality (14) `E_F(σ) ≥ E_F(Tr₂σ) + E_F(Tr₁σ)` holds for every pure state
`σ = |φ⟩⟨φ|`, it holds for every density matrix `σ`.

**Formalization Note.** ("strong subadditivity" in the source is a typo for the strong
superadditivity being reduced.) Pure states are `pureDensity φ` for unit vectors `φ`. The
reduction is for one fixed system: the hypothesis and the conclusion range over states of the
same four spaces. Index and partial-trace conventions are those of
`FormationStronglySuperadditive`. -/
theorem strongSuperadditive_of_pure {A₁ A₂ B₁ B₂ : Type} [Fintype A₁] [DecidableEq A₁]
    [Fintype A₂] [DecidableEq A₂] [Fintype B₁] [DecidableEq B₁] [Fintype B₂] [DecidableEq B₂]
    (h : ∀ φ : EuclideanSpace ℂ ((A₁ × A₂) × (B₁ × B₂)), ‖φ‖ = 1 →
      formation (trTwo (pureDensity φ)) + formation (trOne (pureDensity φ)) ≤
        formation (pureDensity φ))
    (σ : Matrix ((A₁ × A₂) × (B₁ × B₂)) ((A₁ × A₂) × (B₁ × B₂)) ℂ) (hσ : IsDensityMatrix σ) :
    formation (trTwo σ) + formation (trOne σ) ≤ formation σ := by sorry

end ShorAdditivityEquiv
