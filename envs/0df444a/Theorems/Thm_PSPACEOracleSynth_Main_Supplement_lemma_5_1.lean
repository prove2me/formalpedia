-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_lemma_5_1
-- name    : PSPACEOracleSynth.Main.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:36:25.17056+00:00
-- url     : https://prove2.me/theorems/9a2d1688-ece7-4753-a43d-5ca2ca37d815
-- title:
--   Lemma 5.1 — Oracle-free uniform generation of coherent simulations of BQP oracle gates at operator error 2^{−m}.
-- statement:
--   Let $L$ be a classical language and $B\in\mathrm{BQP}^L$. One deterministic polynomial-time algorithm without an oracle maps $(1^\ell,1^m)$, for all $\ell,m\ge1$, to a unitary circuit $C^{\rm sim}_{\ell,m}$ over $G$ with $O_L$ gates, on the query, answer and additional zero ancilla wires. It satisfies
--
--   $$\|C^{\rm sim}_{\ell,m}\iota_a-\iota_a O_B\|\le2^{-m}.$$
--
--   This operator-norm guarantee acts coherently on every unknown query/answer input and returns the ancillas to zero up to the stated error.
--
--   Differences from the source:
--   - encoding: finite qubit registers and normalized states → Bits n, UnitKet and density-matrix predicates, including n=0; reason: basis labels and explicit state predicates change no instance
--   - encoding: oracle-free generators with named input/output wires and unary precision → published TimeUniform and SpaceUniform on tuple codes and canonical current wire labels; reason: renaming live wires and decoding interface counts preserve all circuit families and their polynomial resources
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Lemma 5.1, p. 30

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_OracleSubstitution

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement


/-- Lemma 5.1, p. 30. Generator is oracle free; the generated circuit has O_L gates.
The error is operator norm on the zero-ancilla subspace. -/
theorem lemma_5_1 (L B : Set Str) (hB : B ∈ decisionBQPO (langOracle L)) :
    ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit) (p : Polynomial ℕ), HasFPTEAS f ∧
      TimeUniform (fun lm : ℕ × ℕ => tup [unary lm.1, unary lm.2])
        (fun lm => (C lm.1 lm.2).code) ∧
      ∀ l m, 1 ≤ l → 1 ≤ m → (C l m).Valid f ∧ OverG f (C l m) ∧
        ∃ h : l+1 ≤ (C l m).N, (C l m).N ≤ p.eval (l+m) ∧
          opNormR ((C l m).unitary f (emb (langOracle L)) * ancMat h -
            ancMat h * (emb (langOracle B) (l+1) : Op (Bits (l+1)))) ≤ (2 : ℝ)⁻¹ ^ m := by sorry

end PSPACEOracleSynth.Main.Supplement
