-- Prove2me | Theorems.Thm_WernerExt_TwoSided_symmetric_extensions
-- name    : WernerExt.TwoSided.symmetric_extensions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:27.395252+00:00
-- url     : https://prove2.me/theorems/28f8922d-d04e-406e-9cf7-35d775482e77
-- title:
--   p. 2, Extendibility as a ground state problem — symmetric states are extensions of Werner states, and extendible Werner states have symmetric extensions
-- statement:
--   Let $d\ge2$, $n_A,n_B\ge1$. Call an operator $X$ on the joint system *symmetric* if $U^{\otimes(n_A+n_B)}X\,(U^{\otimes(n_A+n_B)})^\dagger=X$ for every unitary $U\in U(d)$ and $P_{\sigma,\tau}XP_{\sigma,\tau}^\dagger=X$ for every $(\sigma,\tau)\in S_{n_A}\times S_{n_B}$, where $P_{\sigma,\tau}$ permutes Alice's sites by $\sigma$ and Bob's by $\tau$.
--
--   1. Every symmetric state $X$ is an $(n_A,n_B)$-extension of $\rho^W(\alpha)$ for some $\alpha\in[-1,1]$.
--   2. If $\hat\rho$ is an $(n_A,n_B)$-extension of $\rho^W(\alpha)$, then for every unitary $U$ and every $(\sigma,\tau)$, $$W\hat\rho W^\dagger,\qquad W=U^{\otimes(n_A+n_B)}P_{\sigma,\tau},$$ is again an $(n_A,n_B)$-extension of $\rho^W(\alpha)$; hence so is every average of such conjugates, in particular the twirl of $\hat\rho$ over both groups.
--   3. Every $(n_A,n_B)$-extendible Werner state $\rho^W(\alpha)$, $\alpha\in[-1,1]$, has a symmetric $(n_A,n_B)$-extension.
--
--   This lets the search for extensions be restricted to symmetric states, whose structure is governed by representation theory.
--
--   Differences from the source:
--   - reading: the twirl of an extension with the two groups (a Haar average over U(d) and an average over S_{n_A} × S_{n_B}) is an extension of the same Werner state → clause 2: every single conjugate W ρ̂ W† by W = U^{⊗(n_A+n_B)} P_{σ,τ} is an extension of the same Werner state, together with clause 3, the existence of an extension invariant under both groups; reason: the pinned Mathlib has no Haar probability measure on the unitary group; the set of extensions is convex and closed, so clause 2 gives the twirl claim for every averaging measure, and clause 3 is the sentence's stated conclusion
--   - encoding: invariant to local unitary transformations and bipartite permutations → U^{⊗(n_A+n_B)} X U^{⊗(n_A+n_B)†} = X for all U in Matrix.unitaryGroup, and P X P† = X for the permutation matrices of S_{n_A} × S_{n_B}; reason: definition of invariance; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 2, *Extendibility as a ground state problem*, 'All composite states … symmetric extensions'; p. 1, *Extendibility*

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided

open Matrix
open scoped Kronecker ComplexOrder

/-- p. 2, *Extendibility as a ground state problem*: (a) every state on the joint system that
is invariant under all local unitaries `U^{⊗(nA+nB)}` and all bipartite permutations
`S_{nA} × S_{nB}` is an `(nA, nB)`-extension of some Werner state; (b) conjugating an extension
of `ρ_W(α)` by any element of these groups gives an extension of the same `ρ_W(α)` (so every
average of such conjugates, in particular the twirl, is one); (c) every extendible Werner state
has an extension invariant under both groups. -/
theorem symmetric_extensions (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB) :
    (∀ X : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ, X.PosSemidef → X.trace = 1 →
        (∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, localU nA nB U * X * (localU nA nB U)ᴴ = X) →
        (∀ (σ : Equiv.Perm (Fin nA)) (τ : Equiv.Perm (Fin nB)),
          permCfg (d := d) σ τ * X * (permCfg (d := d) σ τ)ᴴ = X) →
        ∃ α ∈ Set.Icc (-1 : ℝ) 1, IsExtensionOf X (wernerState d α)) ∧
      (∀ α ∈ Set.Icc (-1 : ℝ) 1, ∀ X : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ,
        IsExtensionOf X (wernerState d α) →
        ∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ,
        ∀ (σ : Equiv.Perm (Fin nA)) (τ : Equiv.Perm (Fin nB)),
          IsExtensionOf
            ((localU nA nB U * permCfg (d := d) σ τ) * X *
              (localU nA nB U * permCfg (d := d) σ τ)ᴴ) (wernerState d α)) ∧
      (∀ α ∈ Set.Icc (-1 : ℝ) 1, IsExtendible d nA nB (wernerState d α) →
        ∃ X : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ, IsExtensionOf X (wernerState d α) ∧
          (∀ U ∈ Matrix.unitaryGroup (Fin d) ℂ, localU nA nB U * X * (localU nA nB U)ᴴ = X) ∧
          (∀ (σ : Equiv.Perm (Fin nA)) (τ : Equiv.Perm (Fin nB)),
            permCfg (d := d) σ τ * X * (permCfg (d := d) σ τ)ᴴ = X)) := by sorry

end WernerExt.TwoSided
