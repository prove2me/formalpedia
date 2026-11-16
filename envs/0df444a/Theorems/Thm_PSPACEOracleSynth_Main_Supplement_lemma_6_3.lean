-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_lemma_6_3
-- name    : PSPACEOracleSynth.Main.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:32:51.576919+00:00
-- url     : https://prove2.me/theorems/9d8fce14-e10a-4715-9f78-afc2ac56ce58
-- title:
--   Lemma 6.3 — The prescribed square-root-of-Choi map is an isometry and implements the channel after tracing its environment.
-- statement:
--   Let $C$ be a channel from $a$ input qubits to $b$ output qubits. Form its unnormalized Choi matrix in input-first order. Let $E$ have $a+b$ qubits, indexed like the input and output together, and set $Y_{v,i;u}=(\sqrt{J_C})_{u,v;i}$. Then
--
--   $$Y^\dagger Y=I,\qquad \operatorname{Tr}_E(Y\rho Y^\dagger)=C(\rho)\quad\text{for every matrix }\rho.$$
--
--   Thus the prescribed square-root map itself is a Stinespring isometry; the claim is not merely existence of an unspecified dilation.
--
--   Differences from the source:
--   - generalization: the channel C of the general circuit fixed in Section 6.1 → every finite-qubit CPTP channel C; reason: the prescribed Choi formula and both identities hold for every channel and specialize to that circuit
--   - encoding: finite qubit registers and normalized states → Bits n, UnitKet and density-matrix predicates, including n=0; reason: basis labels and explicit state predicates change no instance
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Lemma 6.3, p. 35

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Choi

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement


/-- Lemma 6.3, p. 35: the prescribed square-root Choi map, for every channel.
The statement applies to any channel, hence in particular to the circuit C of §6.1. -/
theorem lemma_6_3 {a b : ℕ} (C : Map (Bits a) (Bits b)) (hC : IsChannel C) :
    (choiIso C)ᴴ * choiIso C = 1 ∧
      ∀ ρ : Op (Bits a), traceRight (choiIso C * ρ * (choiIso C)ᴴ) = C ρ := by sorry

end PSPACEOracleSynth.Main.Supplement
