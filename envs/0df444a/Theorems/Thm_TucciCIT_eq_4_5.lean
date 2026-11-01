-- Prove2me | Theorems.Thm_TucciCIT_eq_4_5
-- name    : TucciCIT.eq_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:31:22.564201+00:00
-- url     : https://prove2.me/theorems/79d95606-41da-4dc2-9e3f-fcb3656ec0dd
-- title:
--   Eqs. (4.5a)–(4.5d) — complementary entropies of the pure meta state
-- statement:
--   Let $\psi$ be a unit amplitude, $\sum_{x,y}|\psi(x,y)|^2 = 1$, and $\mu$ its meta density matrix (4.1), a pure state on $\mathcal H_{x,y,e}$. Then
--
--   1. $S_\mu(x, e) = S_\mu(y)$ (4.5a),
--   2. $S_\mu(y, e) = S_\mu(x)$ (4.5b),
--   3. $S_\mu(x, y, e) = 0$ (4.5c),
--   4. $S_\mu(e) = S_\mu(x, y)$ (4.5d).
--
--   These are the complementary-subsystem identities of a pure tripartite state, used to collapse (4.4) to a mutual information.
--
--   Differences from the source:
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
--   - encoding: S_μ of a set of nodes → subsystemEntropy μ keep forget, with keep the kept coordinates of (e, x, y) in a fixed order; reason: entropy is invariant under reordering the kept registers; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eqs. (4.5a)–(4.5d), p.8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_TucciCIT_metaDensity

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eqs. (4.5a)–(4.5d), p.8 (PDF p.8): "But µ is a pure state acting on
Hx,y,e, so Sµ(x, e) = Sµ(y), Sµ(y, e) = Sµ(x), Sµ(x, y, e) = 0, Sµ(e) = Sµ(x, y)."

Let `ψ` be a unit amplitude, `Σ_{x,y} |ψ(x,y)|² = 1`, and `μ = |ψ_meta⟩⟨ψ_meta|` the meta density
matrix (4.1). Then, all four at once,
1. `S_μ(x, e) = S_μ(y)` (4.5a),
2. `S_μ(y, e) = S_μ(x)` (4.5b),
3. `S_μ(x, y, e) = 0` (4.5c),
4. `S_μ(e) = S_μ(x, y)` (4.5d).

**Formalization Note.** Each `S_μ(A)` is `subsystemEntropy μ keep forget` with `keep` the
coordinates of `A` among `(e, x, y)` and `forget` the rest; `S_μ(x, y, e)` is `vnEntropy μ`. -/
theorem eq_4_5 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ψ : Matrix X Y ℂ) (hψ : ∑ x, ∑ y, ‖ψ x y‖ ^ 2 = 1) :
    subsystemEntropy (metaDensity ψ) (fun p => (p.1, p.2.1)) (fun p => p.2.2) =
        subsystemEntropy (metaDensity ψ) (fun p => p.2.2) (fun p => (p.1, p.2.1)) ∧
      subsystemEntropy (metaDensity ψ) (fun p => (p.1, p.2.2)) (fun p => p.2.1) =
        subsystemEntropy (metaDensity ψ) (fun p => p.2.1) (fun p => (p.1, p.2.2)) ∧
      vnEntropy (metaDensity ψ) = 0 ∧
      subsystemEntropy (metaDensity ψ) (fun p => p.1) (fun p => p.2) =
        subsystemEntropy (metaDensity ψ) (fun p => p.2) (fun p => p.1) := by sorry

end TucciCIT
