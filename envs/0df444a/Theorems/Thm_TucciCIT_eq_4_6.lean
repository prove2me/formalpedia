-- Prove2me | Theorems.Thm_TucciCIT_eq_4_6
-- name    : TucciCIT.eq_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:26.733809+00:00
-- url     : https://prove2.me/theorems/e5b1248f-835d-433d-aa2a-8f37c64b79d2
-- title:
--   Eq. (4.6) — $S_\mu(x:y|e) = S_\mu(x:y) = S_\rho(x:y)$
-- statement:
--   Let $\psi$ be a unit amplitude, $\mu$ its meta density matrix (4.1) and $\rho = \operatorname{tr}_e\mu$ (4.3). Then
--
--   $$
--   S_\mu(x : y|e) = S_\mu(x : y) = S_\rho(x : y),
--   $$
--
--   where $S_\mu(x:y) = S_\mu(x) + S_\mu(y) - S_\mu(x,y)$ and $S_\rho(x:y) = S_\rho(x) + S_\rho(y) - S(\rho)$ are quantum mutual informations of the listeners.
--
--   So conditioning on the speaker does not change the listeners' mutual information for this pure meta state.
--
--   Differences from the source:
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
--   - encoding: S_μ of a set of nodes → subsystemEntropy μ keep forget, with keep the kept coordinates of (e, x, y) in a fixed order; reason: entropy is invariant under reordering the kept registers; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (4.6), p.8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_TucciCIT_metaDensity
import Definitions.Def_TucciCIT_sTanglement

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (4.6), p.8 (PDF p.8): "Substituting Eqs.(4.5) into Eq.(4.4)
yields Sµ(x : y|e) = Sµ(x : y) = Sρ(x : y)."

Let `ψ` be a unit amplitude, `μ` its meta density matrix (4.1) and `ρ = tr_e μ` (4.3). Then
`S_μ(x : y|e) = S_μ(x : y) = S_ρ(x : y)`, where `S_μ(x : y) = S_μ(x) + S_μ(y) − S_μ(x, y)` and
`S_ρ(x : y) = S_ρ(x) + S_ρ(y) − S(ρ)` are quantum mutual informations.

**Formalization Note.** `ρ` is `redistributionMarginal μ (fun p => p.2) (fun p => p.1)`, a matrix
on `X × Y`; `S_ρ(x)` keeps `Prod.fst`, `S_ρ(y)` keeps `Prod.snd`. The two equalities are the two
conjuncts. -/
theorem eq_4_6 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ψ : Matrix X Y ℂ) (hψ : ∑ x, ∑ y, ‖ψ x y‖ ^ 2 = 1) :
    sTanglement (metaDensity ψ) =
        subsystemEntropy (metaDensity ψ) (fun p => p.2.1) (fun p => (p.1, p.2.2)) +
          subsystemEntropy (metaDensity ψ) (fun p => p.2.2) (fun p => (p.1, p.2.1)) -
          subsystemEntropy (metaDensity ψ) (fun p => p.2) (fun p => p.1) ∧
      subsystemEntropy (metaDensity ψ) (fun p => p.2.1) (fun p => (p.1, p.2.2)) +
          subsystemEntropy (metaDensity ψ) (fun p => p.2.2) (fun p => (p.1, p.2.1)) -
          subsystemEntropy (metaDensity ψ) (fun p => p.2) (fun p => p.1) =
        subsystemEntropy (redistributionMarginal (metaDensity ψ) (fun p => p.2) (fun p => p.1))
            Prod.fst Prod.snd +
          subsystemEntropy (redistributionMarginal (metaDensity ψ) (fun p => p.2) (fun p => p.1))
            Prod.snd Prod.fst -
          vnEntropy (redistributionMarginal (metaDensity ψ) (fun p => p.2) (fun p => p.1)) := by sorry

end TucciCIT
