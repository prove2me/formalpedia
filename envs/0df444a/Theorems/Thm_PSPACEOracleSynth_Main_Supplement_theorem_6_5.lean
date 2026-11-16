-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_theorem_6_5
-- name    : PSPACEOracleSynth.Main.Supplement.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:38:24.216452+00:00
-- url     : https://prove2.me/theorems/a39045f7-6ba5-4fbc-9772-e7bedfb8b34d
-- title:
--   Theorem 6.5 — Both channel-model collapse criteria, including the arbitrary-oracle equivalence and all stated particular cases.
-- statement:
--   In the channel model the following all hold.
--
--   1. For every classical language $L$,
--   $$[\forall U\in\mathrm{unitaryPSPACE}^{\diamond},\ U\text{ size-computable}\Rightarrow U\in\mathrm{unitaryBQP}^{\diamond,L}]\ \Longleftrightarrow\ \mathrm{PSPACE}\subseteq\mathrm{BQP}^L.$$
--   In particular, all size-computable polynomial-space problems lie in $\mathrm{unitaryBQP}^{\diamond}$ if and only if $\mathrm{BQP}=\mathrm{PSPACE}$; they all lie in $\mathrm{unitaryBQP}^{\diamond,K}$ for every PSPACE-complete language $K$.
--   2. On all synthesis problems, without assuming size-computability,
--   $$\mathrm{unitaryBQP}^{\diamond}=\mathrm{unitaryPSPACE}^{\diamond}\quad\Longleftrightarrow\quad \mathrm{P}=\mathrm{PSPACE}.$$
--
--   These distinguish the complexity of implementing the channel from the deterministic complexity of computing its register sizes.
--
--   Differences from the source:
--   - encoding: finite qubit registers and normalized states → Bits n, UnitKet and density-matrix predicates, including n=0; reason: basis labels and explicit state predicates change no instance
--   - encoding: real full diamond norm over pure reference-entangled inputs → an extended nonnegative real supremum over all pure inputs and finite qubit references; reason: bounds are identical and the supremum has no empty or unbounded real default
--   - encoding: oracle-free generators with named input/output wires and unary precision → published TimeUniform and SpaceUniform on tuple codes and canonical current wire labels; reason: renaming live wires and decoding interface counts preserve all circuit families and their polynomial resources
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Theorem 6.5, p. 37

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Interaction

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement

/-- Theorem 6.5, p. 37: (i), both particular cases, and (ii), without bundling
size-computability into synthesis problems. The iff scopes over the entire inclusion. -/
theorem theorem_6_5 :
    (∀ L : Set Str,
      ((∀ U ∈ channelPSPACE, SizeComputable U → U ∈ channelBQPO (langOracle L)) ↔
        PSPACE (fun _ => false) ⊆ decisionBQPO (langOracle L))) ∧
    (((∀ U ∈ channelPSPACE, SizeComputable U → U ∈ channelBQP) ↔
      decisionBQP = PSPACE (fun _ => false))) ∧
    (∀ K : Set Str, IsPSPACECompleteRel (fun _ => false) K →
      ∀ U ∈ channelPSPACE, SizeComputable U → U ∈ channelBQPO (langOracle K)) ∧
    ((channelBQP = channelPSPACE) ↔ (decisionP = PSPACE (fun _ => false))) := by sorry

end PSPACEOracleSynth.Main.Supplement
