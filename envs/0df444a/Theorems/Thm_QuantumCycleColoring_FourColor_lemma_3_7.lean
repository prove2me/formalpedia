-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_lemma_3_7
-- name    : QuantumCycleColoring.FourColor.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:00:10.036727+00:00
-- url     : https://prove2.me/theorems/f0bbe731-996d-4ddd-9e12-52890e80a037
-- title:
--   Lemma 3.7: rounding one element of a 4-outcome POVM in $\Lambda$-norm
-- statement:
--   There is a universal constant $K>0$ with the following property. Let $\{P_i\}_{i\in[4]}$ be a 4-outcome POVM on $\mathbb C^N\otimes\mathbb C^N$, let $Z$ be an operator with $0\preceq Z\preceq I$, and let $\Lambda$ be a PSD $N\times N$ matrix with $\|\Lambda\|_F=1$. Write $\varepsilon=\|P_1-Z\|_\Lambda$. Then there is a 4-outcome POVM $\{P'_i\}_{i\in[4]}$ with $P'_1=Z$ and
--   $$\|P_i-P'_i\|_\Lambda\le K\sqrt{\varepsilon}\qquad(2\le i\le 4).$$
--
--   The lemma replaces one element of a POVM by a nearby operator while keeping a POVM and moving the other elements by $O(\sqrt\varepsilon)$ in $\Lambda$-norm; it is the final rounding step of the four-colour proof.
--
--   Differences from the source:
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: outcomes i ∈ [4] = {1,2,3,4}, the distinguished one being P_1 → outcomes Fin 4 = {0,1,2,3}, the distinguished one being P 0; reason: 0-based indexing; the same POVMs
--   - reading: ‖P_i − P'_i‖_Λ = O(√ε) → one explicit constant ∃ K > 0 quantified before every other object (dimension, operators, Λ); reason: the paper's O(·)/Ω(1) constants are absolute; this is the strongest reading
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Lemma 3.7, p.19 (proof in Appendix A.1, pp.50–52)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix

/-- Lemma 3.7, p.19 (Gur–Li, STOC 2027 #515). There is a universal constant `K > 0` such
that: for every 4-outcome POVM `{P_i}` on `ℂ^d ⊗ ℂ^d`, every `Z` with `0 ⪯ Z ⪯ I` and every PSD
`Λ` with `‖Λ‖_F = 1`, writing `ε = ‖P_1 − Z‖_Λ`, there is a 4-outcome POVM `{P'_i}` with
`P'_1 = Z` and `‖P_i − P'_i‖_Λ ≤ K √ε` for `2 ≤ i ≤ 4`. Outcome `1` of the paper is `0 : Fin 4`. -/
theorem lemma_3_7 : ∃ K : ℝ, 0 < K ∧
    ∀ (d : Type) [Fintype d] [DecidableEq d] (P : Fin 4 → Matrix (d × d) (d × d) ℂ),
      FuchsVdGraaf.IsPOVM P →
      ∀ (Z : Matrix (d × d) (d × d) ℂ), Z.PosSemidef → (1 - Z).PosSemidef →
      ∀ (Λ : Matrix d d ℂ), Λ.PosSemidef → frobNorm Λ = 1 →
      ∃ P' : Fin 4 → Matrix (d × d) (d × d) ℂ, FuchsVdGraaf.IsPOVM P' ∧ P' 0 = Z ∧
        ∀ i : Fin 4, i ≠ 0 →
          lamNorm Λ (P i - P' i) ≤ K * Real.sqrt (lamNorm Λ (P 0 - Z)) := by sorry

end QuantumCycleColoring.FourColor
