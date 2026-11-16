-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_lemma_6_4
-- name    : PSPACEOracleSynth.Main.Supplement.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:34:00.810522+00:00
-- url     : https://prove2.me/theorems/69903083-d156-4dc6-aa67-ca414ae1de60
-- title:
--   Lemma 6.4 — Polynomial-space computability of every entry of the specific reflection W constructed on page 35.
-- statement:
--   Let $(C_{x,r})$ be an oracle-free, valid, space-uniform general-circuit family using space polynomial in $|x|+r$. For each member form the explicit Choi isometry and reflection $W_{x,r}=I-Z_{x,r}Z_{x,r}^\dagger$ of Section 6.1. Then
--
--   $$\text{one deterministic machine computes every entry of }W_{x,r}\text{ in polynomial space.}$$
--
--   The entry algorithm receives $x,1^r$, both basis indices and $1^t$, has error at most $2^{-t}$, uses polynomial space in $|x|+r+t$, and writes $O(t+1)$ bits per complex component. This is a uniform claim about the specific reflection, without an assumption of polynomial-time size-computability.
--
--   Differences from the source:
--   - generalization: input and output sizes depend on x in the family fixed on page 35 → input and output sizes may depend on both x and r; reason: polynomial live space bounds both sizes and the same entry algorithm specializes to the x-only family
--   - encoding: oracle-free generators with named input/output wires and unary precision → published TimeUniform and SpaceUniform on tuple codes and canonical current wire labels; reason: renaming live wires and decoding interface counts preserve all circuit families and their polynomial resources
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Lemma 6.4, p. 35

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Choi

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement


/-- Lemma 6.4, p. 35, with the family and W fixed in §6.1. -/
theorem lemma_6_4 (C : Str → ℕ → GeneralCircuit)
    (huniform : SpaceFamily C) (hfree : ∀ x r, (C x r).oracleFree)
    (hvalid : ∀ x r, 1 ≤ r → (C x r).valid) :
    ReflectionEntriesPSpace C := by sorry

end PSPACEOracleSynth.Main.Supplement
