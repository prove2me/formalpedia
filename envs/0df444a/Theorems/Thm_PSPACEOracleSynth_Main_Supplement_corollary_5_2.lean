-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_corollary_5_2
-- name    : PSPACEOracleSynth.Main.Supplement.corollary_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:37:31.094694+00:00
-- url     : https://prove2.me/theorems/5a5cca51-63d3-459c-9348-274c97183bd2
-- title:
--   Corollary 5.2 — BQP oracle substitution for both clean and projective polynomial-time classes, preserving circuits over G.
-- statement:
--   For classical languages $L$ and $B$ with $B\in\mathrm{BQP}^L$,
--
--   $$\mathrm{unitaryP}^B\subseteq\mathrm{unitaryP}^L,\qquad \mathrm{projUnitaryP}^B\subseteq\mathrm{projUnitaryP}^L.$$
--
--   If the witnessing family for either input membership uses only gates over $G$, a witnessing family for the output membership also uses only $G$. Both the clean extension convention and the projective fixed-garbage convention are preserved.
--
--   Differences from the source:
--   - encoding: the published clean and projective classes and their preservation-of-G clause → the immutable published classes and explicit G-refined witnessing-class inclusions; reason: G-refined membership means exactly that a witnessing family over G exists
--   - encoding: families indexed by positive size and precision → published clean and projective classes also include zero size and zero precision; reason: finite boundary members can be synthesized separately; the restriction to positive indices is the source claim
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Corollary 5.2, p. 30

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_OracleSubstitution

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement


/-- Corollary 5.2, p. 30: both inclusions and preservation of the exact gate set G. -/
theorem corollary_5_2 (L B : Set Str) (hB : B ∈ decisionBQPO (langOracle L)) :
    unitaryP (emb (langOracle B)) ⊆ unitaryP (emb (langOracle L)) ∧
      projUnitaryP (langOracle B) ⊆ projUnitaryP (langOracle L) ∧
      ∀ projective : Bool, timeSynthG projective (langOracle B) ⊆
        timeSynthG projective (langOracle L) := by sorry

end PSPACEOracleSynth.Main.Supplement
