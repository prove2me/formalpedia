-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_lemma_4_13
-- name    : UnitaryQIPPSPACE.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:34:10.913286+00:00
-- url     : https://prove2.me/theorems/d4f72ebc-2706-41e5-8340-29dc99771109
-- title:
--   Lemma 4.13 — correction predicates are in PSPACE
-- statement:
--   Let $A\in\mathsf{PSPACE}$. Then the correction language
--   $$\Gamma_A(a_{\le j},x)=\bigoplus_{S\subseteq[j]}h_A(x\oplus a_S),\qquad h_A(y,t)=t\cdot A(y),$$
--   ($\Gamma_A=0$ on illegitimate input) is in $\mathsf{PSPACE}$.
--
--   Hence all resource states of the injection for a PSPACE oracle are phase states of one PSPACE predicate.
--
--   Differences from the source:
--   - encoding: (a_{≤j}, x) "implicitly encoded as a binary string" → tup [tup [a₁, …, a_j], x]; reason: a fixed self-delimiting code, the one Lemma 4.16 and Protocol 4.17 use for (z, x)
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.13, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform
import Definitions.Def_UnitaryQIPPSPACE_GammaLang

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- **Lemma 4.13 (Correction predicates are in PSPACE)** (He, Ou, Zhao, *unitaryQIP =
unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, p. 29 (PDF p. 31)): "Let a language
`A ∈ PSPACE`. For a bitstring `x` with `|x| = ℓ + 1`, we split `x = (y, t)` with `y ∈ {0,1}^ℓ` and
`t ∈ {0,1}`, and define `h_A(y, t) = t · A(y)`. For `j ≥ 0` and a list `a_{≤j} = (a₁, …, a_j)` of `j`
strings of length `|x|` (empty if `j = 0`), implicitly encoded as a binary string, write
`a_S := ⊕_{i ∈ S} a_i` for `S ⊆ [j]`, with `a_∅ = 0^{|x|}`. We define the language
`Γ_A(a_{≤j}, x) := ⊕_{S ⊆ [j]} h_A(x ⊕ a_S)`, and we set `Γ_A = 0` on illegitimate input. Then
`Γ_A ∈ PSPACE`."

**Formalization Note** `PSPACE` is the published `QAdvFew.PoQOracle.PSPACE` with the empty oracle;
the input `(a_{≤j}, x)` is the string `tup [tup [a₁, …, a_j], x]` (see `GammaLang`). -/
theorem lemma_4_13 (A : Set Str) (hA : A ∈ PSPACE noOracle) :
    GammaLang A ∈ PSPACE noOracle := by sorry

end UnitaryQIPPSPACE
