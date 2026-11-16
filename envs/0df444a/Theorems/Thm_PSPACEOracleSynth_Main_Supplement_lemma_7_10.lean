-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_lemma_7_10
-- name    : PSPACEOracleSynth.Main.Supplement.lemma_7_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:43:18.317768+00:00
-- url     : https://prove2.me/theorems/4b1366fe-4f3c-4c6b-9d7a-7abcc863131e
-- title:
--   Lemma 7.10 — Input-dependent channel completions within trace error ε imply one completion within diamond error 2ε.
-- statement:
--   Let $U:A\to B$ be an arbitrary partial isometry and let $C:A\to B$ be a channel. Suppose for every pure input $\psi$ on $AR$ some channel completion $\Phi$ of $U$, possibly depending on $\psi$, satisfies
--
--   $$D((C\otimes\mathrm{id})(\psi),(\Phi\otimes\mathrm{id})(\psi))\le\varepsilon.$$
--
--   Then one channel completion satisfies
--
--   $$\|C-\Phi\|_\diamond\le2\varepsilon.$$
--
--   The conclusion chooses the completion before all inputs. Zero support is allowed.
--
--   Differences from the source:
--   - encoding: finite qubit registers and normalized states → Bits n, UnitKet and density-matrix predicates, including n=0; reason: basis labels and explicit state predicates change no instance
--   - encoding: real full diamond norm over pure reference-entangled inputs → an extended nonnegative real supremum over all pure inputs and finite qubit references; reason: bounds are identical and the supremum has no empty or unbounded real default
--   - encoding: states and unit kets in the mathematical definitions → explicit density and unit-norm predicates; reason: these are the standing state conventions, not extra regularity assumptions
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Lemma 7.10, p. 42

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Quantum

open QAlgorithms QAlgorithms.Complexity
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement


/-- Lemma 7.10, p. 42. Completion may depend on each input in the premise,
but one completion works for all inputs in the diamond-norm conclusion. -/
theorem lemma_7_10 {a b : ℕ} (U : PartialIso a b)
    (C : Map (Bits a) (Bits b)) (hC : IsChannel C) (ε : ℝ)
    (h : ∀ (r : ℕ) (ψ : Bits a × Bits r → ℂ), UnitKet ψ →
      ∃ Φ, Completion U Φ ∧ dist (withRef C (ket ψ)) (withRef Φ (ket ψ)) ≤ ε) :
    ∃ Φ, Completion U Φ ∧ diamond (fun ρ => C ρ - Φ ρ) ≤ ENNReal.ofReal (2*ε) := by sorry

end PSPACEOracleSynth.Main.Supplement
